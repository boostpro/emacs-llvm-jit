/* Compilation of byte code to LLVM IR.
   Copyright (C) 2012 BoostPro Computing, Inc.

This file is not part of GNU Emacs. */

/* Created by John Wiegley <johnw@boostpro.com> */

#define GNULIB_defined_struct_option 1
#define GNULIB_defined_struct__gl_verify_type 1

extern "C" {

#define WINDOW_H_INCLUDED
#define COMPILING_LLVM_CPP

#define class em_class
#include "bytecode.c"
#undef class
#undef PT
#undef free
#undef malloc
#undef realloc

void *malloc(size_t);
void *realloc(void *, size_t);
void free(void *);

}

#include <vector>
#include <map>
#include <algorithm>
#include <tr1/functional>
#include <tr1/type_traits>
#include <tr1/cstdint>

#include <llvm/LLVMContext.h>
#include <llvm/Module.h>
#include <llvm/PassManager.h>
#include <llvm/Function.h>
#include <llvm/CallingConv.h>
#include <llvm/DerivedTypes.h>
#include <llvm/Analysis/Verifier.h>
#include <llvm/Analysis/Passes.h>
#include <llvm/Target/TargetData.h>
#include <llvm/Transforms/Scalar.h>
#include <llvm/Assembly/PrintModulePass.h>
#include <llvm/Support/IRBuilder.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/ExecutionEngine/ExecutionEngine.h>
#include <llvm/ExecutionEngine/JIT.h>

#define PT (current_buffer->pt + 0)

using namespace std;
using namespace std::tr1;
using namespace llvm;

namespace lc
{
  static Module *              TheModule = NULL;
  static Function *            TheFunction = NULL;
  static ExecutionEngine *     TheExecutionEngine;
  static FunctionPassManager * TheFPM;
  static LLVMContext *         Context;
  static IRBuilder<> *         Builder;

  struct UChar {
    typedef unsigned char value_type;
    typedef ConstantInt llvm_constant_type;
    Type *operator()() {
      return Type::getInt8Ty(*Context);
    }
  };

  struct Double {
    typedef double value_type;
    Type *operator()() {
      return Type::getDoubleTy(*Context);
    }
  };

  struct LispObject {
    typedef Lisp_Object value_type;
    Type *operator()() {
      return Type::getInt64Ty(*Context);
    }
  };

  template <typename T>
  struct If
  {
    BasicBlock * then_block;
    BasicBlock * else_block;
    BasicBlock * ifend;
    Value *      condbr;
    Value *      then_body;
    Value *      else_body;

    If(Value *cond, bool has_else = false) : condbr(NULL) {
      then_block = BasicBlock::Create(*Context, "then", TheFunction);
      else_block = has_else ? BasicBlock::Create(*Context, "else") : NULL;
      ifend      = BasicBlock::Create(*Context, "ifend");

      condbr = Builder->CreateCondBr(
        cond, then_block, else_block ? else_block : ifend);
    }

    If& Then(function<Value *()> f) {
      Builder->SetInsertPoint(then_block);

      then_body = f();

      Builder->CreateBr(ifend);
      // Codegen of 'Then' can change the current block, update
      // then_block.
      then_block = Builder->GetInsertBlock();

      return *this;
    }

    If& Else(function<Value *()> f) {
      TheFunction->getBasicBlockList().push_back(else_block);
      Builder->SetInsertPoint(else_block);

      else_body = f();

      Builder->CreateBr(ifend);
      // Codegen of 'Then' can change the current block, update
      // then_block.
      else_block = Builder->GetInsertBlock();

      return *this;
    }

    Value *End() {
      TheFunction->getBasicBlockList().push_back(ifend);
      Builder->SetInsertPoint(ifend);

      PHINode *PN = Builder->CreatePHI(T()(), 2, "iftmp");
      PN->addIncoming(then_body, then_block);
      PN->addIncoming(else_body, else_block);
      return PN;
    }
  };

  struct Node
  {
    Value *value;
    Node(Value *v) : value(v) {}

    operator Value *() {
      return getValue();
    }
    Value * getValue() {
      return value;
    }

    Node operator==(const Node& rhs) {
      return Builder->CreateICmpEQ(*this, const_cast<Node&>(rhs), "tmp");
    }
    Node operator>>(uint64_t size) {
      return Builder->CreateAShr(value, size, "tmp");
    }
  };

  template <typename T>
  struct Constant
  {
    typename T::value_type constant;
    Constant(typename T::value_type c) : constant(c) {}

    operator Value *() {
      return typename T::llvm_constant_type::get (
        T()(), constant,
        /* isSigned= */ is_signed<typename T::value_type>::value);
    }
  };

  struct Obj : Constant<LispObject> {
    Obj(Lisp_Object obj) : Constant<LispObject>(obj) {}
  };

  template <typename ReturnType>
  Node Call(vector<Node>& nodes, const char *Name) {
    // Look up the name in the global module table.
    Function *Callee = TheModule->getFunction(Name);
    if (Callee == 0) {
      vector<Type *> types;
      for_each(
        nodes.begin(), nodes.end(),
        [](Node& node) { types.push_back(node.getValue()->getType()); });

      FunctionType *FT =
        FunctionType::get (/* Result=   */ ReturnType()(),
                           /* Params=   */ types,
                           /* isVarArg= */ false);

      Callee = Function::Create (
        FT, Function::ExternalLinkage, Name, TheModule);
      Callee->setCallingConv(CallingConv::C);
    }

    vector<Value *> values;
    for_each(
      nodes.begin(), nodes.end(),
      [](Node& node) { values.push_back(node.getValue()); });

    return Builder->CreateCall(Callee, values, Name);
  }

  template <typename ReturnType, typename ArgType, typename ...ArgTypes>
  Node Call(
    vector<Node>& nodes, const char *Name, ArgType arg, ArgTypes ...args) {
    nodes.push_back(arg);
    return Call(nodes, Name, args...);
  }

  template <typename ReturnType, typename ...ArgTypes>
  Node Call(const char *Name, ArgTypes ...args) {
    vector<Node> nodes;
    return Call(nodes, args...);
  }
}

using namespace lc;

Value *CompileByteCode (Function *F, Lisp_Object bytestr, Lisp_Object constants,
                        ptrdiff_t nargs, Lisp_Object *args)
{
  int count = SPECPDL_INDEX ();
  int op;
  Lisp_Object *constantsp;
  Lisp_Object *top;
  Lisp_Object result;
  unsigned char *stream = SDATA (bytestr);
  unsigned char *stream_pc = stream;

  CHECK_STRING (bytestr);
  CHECK_VECTOR (constants);

  if (STRING_MULTIBYTE (bytestr))
    /* BYTESTR must have been produced by Emacs 20.2 or the earlier
       because they produced a raw 8-bit string for byte-code and now
       such a byte-code string is loaded as multibyte while raw 8-bit
       characters converted to multibyte form.  Thus, now we must
       convert them back to the originally intended unibyte form.  */
    bytestr = Fstring_as_unibyte (bytestr);

  constantsp = XVECTOR (constants)->contents;

  vector<Node> values;

#if 0
  while (1)
  {
    op = FETCH;

    switch (op)
    {
    case Bvarref + 7:
      op = FETCH2;
      goto varref;

    case Bvarref:
    case Bvarref + 1:
    case Bvarref + 2:
    case Bvarref + 3:
    case Bvarref + 4:
    case Bvarref + 5:
      op = op - Bvarref;
      goto varref;

      /* This seems to be the most frequently executed byte-code
         among the Bvarref's, so avoid a goto here.  */
    case Bvarref+6:
      op = FETCH;
    varref:
      {
        Lisp_Object v1, v2;

        v1 = constantsp[op];
        if (SYMBOLP (v1))
        {
          if (XSYMBOL (v1)->redirect != SYMBOL_PLAINVAL
              || (v2 = SYMBOL_VAL (XSYMBOL (v1)),
                  EQ (v2, Qunbound)))
          {
            v2 = Fsymbol_value (v1);
          }
        }
        else
        {
          v2 = Fsymbol_value (v1);
        }
        PUSH (v2);
        break;
      }

    case Bgotoifnil:
    {
      Lisp_Object v1;
      MAYBE_GC ();
      op = FETCH2;
      v1 = POP;
      if (NILP (v1))
      {
        BYTE_CODE_QUIT;
        stream_pc = stream + op;
      }
      break;
    }

    case Bcar:
      // {
      //   Lisp_Object v1;
      //   v1 = TOP;
      //   if (CONSP (v1))
      //     TOP = XCAR (v1);
      //   else if (NILP (v1))
      //     TOP = Qnil;
      //   else
      //     {
      //       BEFORE_POTENTIAL_GC ();
      //       wrong_type_argument (Qlistp, v1);
      //       AFTER_POTENTIAL_GC ();
      //     }
      //   break;
      // }
    {
      values.front() =
        If<LispObject>((values.front() >> VALBITS) ==
                       Constant<UChar>(Lisp_Cons),
                       /* has_else= */ true)
        .Then ([]() {
          })
        .Else ([]() {
            If<LispObject>(values.front() == Obj(Qnil)),
            /* has_else= */ true)
            .Then ([]() {
                return Obj(Qnil);
              })
            .Else ([]() {
                return Call("wrong_type_argument", Obj(Qlistp),
                            values.front());
              })
            .End ()
          })
        .End ()
      break;
    }

    case Beq:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = EQ (v1, TOP) ? Qt : Qnil;
      break;
    }

    case Bmemq:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Fmemq (TOP, v1);
      break;
    }

    case Bcdr:
    {
      Lisp_Object v1;
      v1 = TOP;
      if (CONSP (v1))
        TOP = XCDR (v1);
      else if (NILP (v1))
        TOP = Qnil;
      else
      {
        wrong_type_argument (Qlistp, v1);
      }
      break;
      break;
    }

    case Bvarset:
    case Bvarset+1:
    case Bvarset+2:
    case Bvarset+3:
    case Bvarset+4:
    case Bvarset+5:
      op -= Bvarset;
      goto varset;

    case Bvarset+7:
      op = FETCH2;
      goto varset;

    case Bvarset+6:
      op = FETCH;
    varset:
      {
        Lisp_Object sym, val;

        sym = constantsp[op];
        val = TOP;

        /* Inline the most common case.  */
        if (SYMBOLP (sym)
            && !EQ (val, Qunbound)
            && !XSYMBOL (sym)->redirect
            && !SYMBOL_CONSTANT_P (sym))
          XSYMBOL (sym)->val.value = val;
        else
        {
          set_internal (sym, val, Qnil, 0);
        }
      }
      (void) POP;
      break;

    case Bdup:
    {
      Lisp_Object v1;
      v1 = TOP;
      PUSH (v1);
      break;
    }

    /* ------------------ */

    case Bvarbind+6:
      op = FETCH;
      goto varbind;

    case Bvarbind+7:
      op = FETCH2;
      goto varbind;

    case Bvarbind:
    case Bvarbind+1:
    case Bvarbind+2:
    case Bvarbind+3:
    case Bvarbind+4:
    case Bvarbind+5:
      op -= Bvarbind;
    varbind:
      /* Specbind can signal and thus GC.  */
      specbind (constantsp[op], POP);
      break;

    case Bcall+6:
      op = FETCH;
      goto docall;

    case Bcall+7:
      op = FETCH2;
      goto docall;

    case Bcall:
    case Bcall+1:
    case Bcall+2:
    case Bcall+3:
    case Bcall+4:
    case Bcall+5:
      op -= Bcall;
    docall:
      {
        DISCARD (op);
        TOP = Ffuncall (op + 1, &TOP);
        break;
      }

    case Bunbind+6:
      op = FETCH;
      goto dounbind;

    case Bunbind+7:
      op = FETCH2;
      goto dounbind;

    case Bunbind:
    case Bunbind+1:
    case Bunbind+2:
    case Bunbind+3:
    case Bunbind+4:
    case Bunbind+5:
      op -= Bunbind;
    dounbind:
      unbind_to (SPECPDL_INDEX () - op, Qnil);
      break;

    case Bunbind_all:	/* Obsolete.  Never used.  */
      /* To unbind back to the beginning of this frame.  Not used yet,
         but will be needed for tail-recursion elimination.  */
      unbind_to (count, Qnil);
      break;

    case Bgoto:
      MAYBE_GC ();
      BYTE_CODE_QUIT;
      op = FETCH2;    /* pc = FETCH2 loses since FETCH2 contains pc++ */
      stream_pc = stream + op;
      break;

    case Bgotoifnonnil:
    {
      Lisp_Object v1;
      MAYBE_GC ();
      op = FETCH2;
      v1 = POP;
      if (!NILP (v1))
      {
        BYTE_CODE_QUIT;
        stream_pc = stream + op;
      }
      break;
    }

    case Bgotoifnilelsepop:
      MAYBE_GC ();
      op = FETCH2;
      if (NILP (TOP))
      {
        BYTE_CODE_QUIT;
        stream_pc = stream + op;
      }
      else DISCARD (1);
      break;

    case Bgotoifnonnilelsepop:
      MAYBE_GC ();
      op = FETCH2;
      if (!NILP (TOP))
      {
        BYTE_CODE_QUIT;
        stream_pc = stream + op;
      }
      else DISCARD (1);
      break;

    case BRgoto:
      MAYBE_GC ();
      BYTE_CODE_QUIT;
      stream_pc += (int) *stream_pc - 127;
      break;

    case BRgotoifnil:
    {
      Lisp_Object v1;
      MAYBE_GC ();
      v1 = POP;
      if (NILP (v1))
      {
        BYTE_CODE_QUIT;
        stream_pc += (int) *stream_pc - 128;
      }
      stream_pc++;
      break;
    }

    case BRgotoifnonnil:
    {
      Lisp_Object v1;
      MAYBE_GC ();
      v1 = POP;
      if (!NILP (v1))
      {
        BYTE_CODE_QUIT;
        stream_pc += (int) *stream_pc - 128;
      }
      stream_pc++;
      break;
    }

    case BRgotoifnilelsepop:
      MAYBE_GC ();
      op = *stream_pc++;
      if (NILP (TOP))
      {
        BYTE_CODE_QUIT;
        stream_pc += op - 128;
      }
      else DISCARD (1);
      break;

    case BRgotoifnonnilelsepop:
      MAYBE_GC ();
      op = *stream_pc++;
      if (!NILP (TOP))
      {
        BYTE_CODE_QUIT;
        stream_pc += op - 128;
      }
      else DISCARD (1);
      break;

    case Breturn:
      result = POP;
      goto exit;

    case Bdiscard:
      DISCARD (1);
      break;

    case Bconstant2:
      PUSH (constantsp[FETCH2]);
      break;

    case Bsave_excursion:
      record_unwind_protect (save_excursion_restore,
                             save_excursion_save ());
      break;

    case Bsave_current_buffer: /* Obsolete since ??.  */
    case Bsave_current_buffer_1:
      record_unwind_protect (set_buffer_if_live, Fcurrent_buffer ());
      break;

    case Bsave_window_excursion: /* Obsolete since 24.1.  */
    {
      register int count1 = SPECPDL_INDEX ();
      record_unwind_protect (Fset_window_configuration,
                             Fcurrent_window_configuration (Qnil));
      TOP = Fprogn (TOP);
      unbind_to (count1, TOP);
      break;
    }

    case Bsave_restriction:
      record_unwind_protect (save_restriction_restore,
                             save_restriction_save ());
      break;

    case Bcatch:		/* FIXME: ill-suited for lexbind.  */
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = internal_catch (TOP, eval_sub, v1);
      break;
    }

    case Bunwind_protect:	/* FIXME: avoid closure for lexbind.  */
      record_unwind_protect (Fprogn, POP);
      break;

    case Bcondition_case:	/* FIXME: ill-suited for lexbind.  */
    {
      Lisp_Object handlers, body;
      handlers = POP;
      body = POP;
      TOP = internal_lisp_condition_case (TOP, body, handlers);
      break;
    }

    case Btemp_output_buffer_setup: /* Obsolete since 24.1.  */
      CHECK_STRING (TOP);
      temp_output_buffer_setup (SSDATA (TOP));
      TOP = Vstandard_output;
      break;

    case Btemp_output_buffer_show: /* Obsolete since 24.1.  */
    {
      Lisp_Object v1;
      v1 = POP;
      temp_output_buffer_show (TOP);
      TOP = v1;
      /* pop binding of standard-output */
      unbind_to (SPECPDL_INDEX () - 1, Qnil);
      break;
    }

    case Bnth:
    {
      Lisp_Object v1, v2;
      v1 = POP;
      v2 = TOP;
      CHECK_NUMBER (v2);
      op = XINT (v2);
      immediate_quit = 1;
      while (--op >= 0 && CONSP (v1))
        v1 = XCDR (v1);
      immediate_quit = 0;
      TOP = CAR (v1);
      break;
    }

    case Bsymbolp:
      TOP = SYMBOLP (TOP) ? Qt : Qnil;
      break;

    case Bconsp:
      TOP = CONSP (TOP) ? Qt : Qnil;
      break;

    case Bstringp:
      TOP = STRINGP (TOP) ? Qt : Qnil;
      break;

    case Blistp:
      TOP = CONSP (TOP) || NILP (TOP) ? Qt : Qnil;
      break;

    case Bnot:
      TOP = NILP (TOP) ? Qt : Qnil;
      break;

    case Bcons:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Fcons (TOP, v1);
      break;
    }

    case Blist1:
      TOP = Fcons (TOP, Qnil);
      break;

    case Blist2:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Fcons (TOP, Fcons (v1, Qnil));
      break;
    }

    case Blist3:
      DISCARD (2);
      TOP = Flist (3, &TOP);
      break;

    case Blist4:
      DISCARD (3);
      TOP = Flist (4, &TOP);
      break;

    case BlistN:
      op = FETCH;
      DISCARD (op - 1);
      TOP = Flist (op, &TOP);
      break;

    case Blength:
      TOP = Flength (TOP);
      break;

    case Baref:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Faref (TOP, v1);
      break;
    }

    case Baset:
    {
      Lisp_Object v1, v2;
      v2 = POP; v1 = POP;
      TOP = Faset (TOP, v1, v2);
      break;
    }

    case Bsymbol_value:
      TOP = Fsymbol_value (TOP);
      break;

    case Bsymbol_function:
      TOP = Fsymbol_function (TOP);
      break;

    case Bset:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Fset (TOP, v1);
      break;
    }

    case Bfset:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Ffset (TOP, v1);
      break;
    }

    case Bget:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Fget (TOP, v1);
      break;
    }

    case Bsubstring:
    {
      Lisp_Object v1, v2;
      v2 = POP; v1 = POP;
      TOP = Fsubstring (TOP, v1, v2);
      break;
    }

    case Bconcat2:
      DISCARD (1);
      TOP = Fconcat (2, &TOP);
      break;

    case Bconcat3:
      DISCARD (2);
      TOP = Fconcat (3, &TOP);
      break;

    case Bconcat4:
      DISCARD (3);
      TOP = Fconcat (4, &TOP);
      break;

    case BconcatN:
      op = FETCH;
      DISCARD (op - 1);
      TOP = Fconcat (op, &TOP);
      break;

    case Bsub1:
    {
      Lisp_Object v1;
      v1 = TOP;
      if (INTEGERP (v1))
      {
        XSETINT (v1, XINT (v1) - 1);
        TOP = v1;
      }
      else
      {
        TOP = Fsub1 (v1);
      }
      break;
    }

    case Badd1:
    {
      Lisp_Object v1;
      v1 = TOP;
      if (INTEGERP (v1))
      {
        XSETINT (v1, XINT (v1) + 1);
        TOP = v1;
      }
      else
      {
        TOP = Fadd1 (v1);
      }
      break;
    }

    case Beqlsign:
    {
      Lisp_Object v1, v2;
      v2 = POP; v1 = TOP;
      CHECK_NUMBER_OR_FLOAT_COERCE_MARKER (v1);
      CHECK_NUMBER_OR_FLOAT_COERCE_MARKER (v2);
      if (FLOATP (v1) || FLOATP (v2))
      {
        double f1, f2;

        f1 = (FLOATP (v1) ? XFLOAT_DATA (v1) : XINT (v1));
        f2 = (FLOATP (v2) ? XFLOAT_DATA (v2) : XINT (v2));
        TOP = (f1 == f2 ? Qt : Qnil);
      }
      else
        TOP = (XINT (v1) == XINT (v2) ? Qt : Qnil);
      break;
    }

    case Bgtr:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Fgtr (TOP, v1);
      break;
    }

    case Blss:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Flss (TOP, v1);
      break;
    }

    case Bleq:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Fleq (TOP, v1);
      break;
    }

    case Bgeq:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Fgeq (TOP, v1);
      break;
    }

    case Bdiff:
      DISCARD (1);
      TOP = Fminus (2, &TOP);
      break;

    case Bnegate:
    {
      Lisp_Object v1;
      v1 = TOP;
      if (INTEGERP (v1))
      {
        XSETINT (v1, - XINT (v1));
        TOP = v1;
      }
      else
      {
        TOP = Fminus (1, &TOP);
      }
      break;
    }

    case Bplus:
      DISCARD (1);
      TOP = Fplus (2, &TOP);
      break;

    case Bmax:
      DISCARD (1);
      TOP = Fmax (2, &TOP);
      break;

    case Bmin:
      DISCARD (1);
      TOP = Fmin (2, &TOP);
      break;

    case Bmult:
      DISCARD (1);
      TOP = Ftimes (2, &TOP);
      break;

    case Bquo:
      DISCARD (1);
      TOP = Fquo (2, &TOP);
      break;

    case Brem:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Frem (TOP, v1);
      break;
    }

    case Bpoint:
    {
      Lisp_Object v1;
      XSETFASTINT (v1, PT);
      PUSH (v1);
      break;
    }

    case Bgoto_char:
      TOP = Fgoto_char (TOP);
      break;

    case Binsert:
      TOP = Finsert (1, &TOP);
      break;

    case BinsertN:
      op = FETCH;
      DISCARD (op - 1);
      TOP = Finsert (op, &TOP);
      break;

    case Bpoint_max:
    {
      Lisp_Object v1;
      XSETFASTINT (v1, ZV);
      PUSH (v1);
      break;
    }

    case Bpoint_min:
    {
      Lisp_Object v1;
      XSETFASTINT (v1, BEGV);
      PUSH (v1);
      break;
    }

    case Bchar_after:
      TOP = Fchar_after (TOP);
      break;

    case Bfollowing_char:
    {
      Lisp_Object v1;
      v1 = Ffollowing_char ();
      PUSH (v1);
      break;
    }

    case Bpreceding_char:
    {
      Lisp_Object v1;
      v1 = Fprevious_char ();
      PUSH (v1);
      break;
    }

    case Bcurrent_column:
    {
      Lisp_Object v1;
      XSETFASTINT (v1, current_column ());
      PUSH (v1);
      break;
    }

    case Bindent_to:
      TOP = Findent_to (TOP, Qnil);
      break;

    case Beolp:
      PUSH (Feolp ());
      break;

    case Beobp:
      PUSH (Feobp ());
      break;

    case Bbolp:
      PUSH (Fbolp ());
      break;

    case Bbobp:
      PUSH (Fbobp ());
      break;

    case Bcurrent_buffer:
      PUSH (Fcurrent_buffer ());
      break;

    case Bset_buffer:
      TOP = Fset_buffer (TOP);
      break;

    case Binteractive_p:	/* Obsolete since 24.1.  */
      PUSH (Finteractive_p ());
      break;

    case Bforward_char:
      TOP = Fforward_char (TOP);
      break;

    case Bforward_word:
      TOP = Fforward_word (TOP);
      break;

    case Bskip_chars_forward:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Fskip_chars_forward (TOP, v1);
      break;
    }

    case Bskip_chars_backward:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Fskip_chars_backward (TOP, v1);
      break;
    }

    case Bforward_line:
      TOP = Fforward_line (TOP);
      break;

    case Bchar_syntax:
    {
      int c;

      CHECK_CHARACTER (TOP);
      c = XFASTINT (TOP);
      if (NILP (BVAR (current_buffer, enable_multibyte_characters)))
        MAKE_CHAR_MULTIBYTE (c);
      XSETFASTINT (TOP, syntax_code_spec[(int) SYNTAX (c)]);
    }
    break;

    case Bbuffer_substring:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Fbuffer_substring (TOP, v1);
      break;
    }

    case Bdelete_region:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Fdelete_region (TOP, v1);
      break;
    }

    case Bnarrow_to_region:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Fnarrow_to_region (TOP, v1);
      break;
    }

    case Bwiden:
      PUSH (Fwiden ());
      break;

    case Bend_of_line:
      TOP = Fend_of_line (TOP);
      break;

    case Bset_marker:
    {
      Lisp_Object v1, v2;
      v1 = POP;
      v2 = POP;
      TOP = Fset_marker (TOP, v2, v1);
      break;
    }

    case Bmatch_beginning:
      TOP = Fmatch_beginning (TOP);
      break;

    case Bmatch_end:
      TOP = Fmatch_end (TOP);
      break;

    case Bupcase:
      TOP = Fupcase (TOP);
      break;

    case Bdowncase:
      TOP = Fdowncase (TOP);
      break;

    case Bstringeqlsign:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Fstring_equal (TOP, v1);
      break;
    }

    case Bstringlss:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Fstring_lessp (TOP, v1);
      break;
    }

    case Bequal:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Fequal (TOP, v1);
      break;
    }

    case Bnthcdr:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Fnthcdr (TOP, v1);
      break;
    }

    case Belt:
    {
      Lisp_Object v1, v2;
      if (CONSP (TOP))
      {
        /* Exchange args and then do nth.  */
        v2 = POP;
        v1 = TOP;
        CHECK_NUMBER (v2);
        op = XINT (v2);
        immediate_quit = 1;
        while (--op >= 0 && CONSP (v1))
          v1 = XCDR (v1);
        immediate_quit = 0;
        TOP = CAR (v1);
      }
      else
      {
        v1 = POP;
        TOP = Felt (TOP, v1);
      }
      break;
    }

    case Bmember:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Fmember (TOP, v1);
      break;
    }

    case Bassq:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Fassq (TOP, v1);
      break;
    }

    case Bnreverse:
      TOP = Fnreverse (TOP);
      break;

    case Bsetcar:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Fsetcar (TOP, v1);
      break;
    }

    case Bsetcdr:
    {
      Lisp_Object v1;
      v1 = POP;
      TOP = Fsetcdr (TOP, v1);
      break;
    }

    case Bcar_safe:
    {
      Lisp_Object v1;
      v1 = TOP;
      TOP = CAR_SAFE (v1);
      break;
    }

    case Bcdr_safe:
    {
      Lisp_Object v1;
      v1 = TOP;
      TOP = CDR_SAFE (v1);
      break;
    }

    case Bnconc:
      DISCARD (1);
      TOP = Fnconc (2, &TOP);
      break;

    case Bnumberp:
      TOP = (NUMBERP (TOP) ? Qt : Qnil);
      break;

    case Bintegerp:
      TOP = INTEGERP (TOP) ? Qt : Qnil;
      break;

    case 0:
      /* Actually this is Bstack_ref with offset 0, but we use Bdup
         for that instead.  */
      /* case Bstack_ref: */
      abort ();

      /* Handy byte-codes for lexical binding.  */
    case Bstack_ref+1:
    case Bstack_ref+2:
    case Bstack_ref+3:
    case Bstack_ref+4:
    case Bstack_ref+5:
    {
      Lisp_Object *ptr = top - (op - Bstack_ref);
      PUSH (*ptr);
      break;
    }
    case Bstack_ref+6:
    {
      Lisp_Object *ptr = top - (FETCH);
      PUSH (*ptr);
      break;
    }
    case Bstack_ref+7:
    {
      Lisp_Object *ptr = top - (FETCH2);
      PUSH (*ptr);
      break;
    }
    case Bstack_set:
      /* stack-set-0 = discard; stack-set-1 = discard-1-preserve-tos.  */
    {
      Lisp_Object *ptr = top - (FETCH);
      *ptr = POP;
      break;
    }
    case Bstack_set2:
    {
      Lisp_Object *ptr = top - (FETCH2);
      *ptr = POP;
      break;
    }
    case BdiscardN:
      op = FETCH;
      if (op & 0x80)
      {
        op &= 0x7F;
        top[-op] = TOP;
      }
      DISCARD (op);
      break;

    case 255:
    default:
      PUSH (constantsp[op - Bconstant]);
    }
  }
#endif

 exit:

  /* Binds and unbinds are supposed to be compiled balanced.  */
  if (SPECPDL_INDEX () != count)
    abort ();

  return NULL /*result*/;
}

Function *CompileFunction (Function *F, Lisp_Object bytestr,
                           Lisp_Object constants,
                           ptrdiff_t nargs, Lisp_Object *args)
{
  // Create a new basic block to start insertion into.
  BasicBlock *BB = BasicBlock::Create(*Context, "entry", F);
  Builder->SetInsertPoint(BB);

  if (Value *RetVal = CompileByteCode(F, bytestr, constants, nargs, args))
    {
      // Finish off the function.
      Builder->CreateRet(RetVal);

      // Validate the generated code, checking for consistency.
      verifyFunction(*F);

      // Optimize the function.
      TheFPM->run(*F);

      return F;
    }

  // Error reading body, remove function.
  F->eraseFromParent();
  return 0;
}

Function *CreateFunction (const char *name, ptrdiff_t nargs, void *id = NULL)
{
  Type ** LispTypes = new Type *[nargs + 1];
  for (int i = 0; i < nargs; ++i)
    LispTypes[i] = Type::getInt64Ty (*Context);
  LispTypes[nargs] = NULL;

  FunctionType *FT =
    /* jww (2012-06-25): Use getInt32Ty when appropriate */
    FunctionType::get (/* Result=   */ Type::getInt64Ty (*Context),
                       /* Params=   */ ArrayRef<Type *>(LispTypes, nargs),
                       /* isVarArg= */ false);
  delete[] LispTypes;

  static char Name[32];
  if (!name)
    sprintf (Name, "__emacs_%p", id);

  Function *F = Function::Create (FT, Function::ExternalLinkage,
                                  name ? name : Name, TheModule);
  F->setCallingConv(CallingConv::C);

  if (!name)
  {
    // Set names for all arguments.
    unsigned idx = 0;
    for (Function::arg_iterator AI = F->arg_begin(); idx != nargs;
         ++AI, ++idx)
      {
        sprintf (Name, "__arg%d", idx);
        AI->setName(Name);
      }
  }

  return F;
}

extern "C" {

void *
llvm_compile_byte_code (Lisp_Object bytestr, Lisp_Object constants,
                        ptrdiff_t nargs, Lisp_Object *args)
{
  //printf("step 0..\n");
  if (! TheModule)
    {
      //printf("step 1..\n");
      InitializeNativeTarget();
      //printf("step 2..\n");
      Context = &getGlobalContext();
      //printf("step 3..\n");
      TheModule = new Module("Emacs-LLVM-JIT", *Context);
      //printf("step 4..\n");
      Builder = new IRBuilder<>(*Context);
      //printf("step 5..\n");

      // Create the JIT.  This takes ownership of the module.
      TheExecutionEngine = EngineBuilder(TheModule).create();
      //printf("step 6..\n");

      FunctionPassManager OurFPM(TheModule);
      //printf("step 7..\n");

      // Set up the optimizer pipeline.  Start with registering info
      // about how the target lays out data structures.
      OurFPM.add(new TargetData(*TheExecutionEngine->getTargetData()));
      //printf("step 8..\n");
      // Provide basic AliasAnalysis support for GVN.
      OurFPM.add(createBasicAliasAnalysisPass());
      //printf("step 9..\n");
      // Do simple "peephole" optimizations and bit-twiddling optzns.
      OurFPM.add(createInstructionCombiningPass());
      //printf("step 10..\n");
      // Reassociate expressions.
      OurFPM.add(createReassociatePass());
      //printf("step 11..\n");
      // Eliminate Common SubExpressions.
      OurFPM.add(createGVNPass());
      //printf("step 12..\n");
      // Simplify the control flow graph (deleting unreachable blocks, etc).
      OurFPM.add(createCFGSimplificationPass());
      //printf("step 13..\n");

      OurFPM.doInitialization();
      //printf("step 14..\n");

      // Set the global so the code gen can use this.
      TheFPM = &OurFPM;
      //printf("step 15..\n");

      /* Create mappings for all of the Emacs Lisp builtins. */
#define MAP_TO_LLVM(name, nargs)                                          \
      {                                                                   \
        Lisp_Object sym =                                                 \
          intern_c_string (const_cast<char *>(#name));                    \
        TheExecutionEngine->addGlobalMapping(                             \
          CreateFunction(#name, nargs),                                   \
          (void *) XSUBR (XSYMBOL (sym)->function)->function.a ## nargs); \
      }

#define MAP_TO_LLVM_N(name)                                               \
      {                                                                   \
        Lisp_Object sym =                                                 \
          intern_c_string (const_cast<char *>(#name));                    \
        Lisp_Object fun = XSYMBOL (sym)->function;                        \
        Lisp_Subr * sub = XSUBR (fun);                                    \
        TheExecutionEngine->addGlobalMapping(                             \
          CreateFunction(#name, sub->max_args),                           \
          (void *) sub->function.aMANY);                                  \
      }

      MAP_TO_LLVM_N(funcall);

      MAP_TO_LLVM(setcar, 2);
    }

  return CompileFunction(CreateFunction(NULL, nargs, (void *) &bytestr),
                         bytestr, constants, nargs, args);
}

Lisp_Object Qllvm_jit_compile;

void
syms_of_lllvm (void)
{
  DEFVAR_BOOL ("llvm-jit-compile", llvm_jit_compile,
	       doc: /* If non-nil, compile byte-code functions with the LLVM JIT. */);

  llvm_jit_compile = 0;

  DEFSYM (Qllvm_jit_compile, "llvm-jit-compile");
}

} // extern "C"
