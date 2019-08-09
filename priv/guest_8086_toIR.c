#include <stdio.h>
#include "libvex_basictypes.h"
#include "libvex_ir.h"
#include "libvex.h"
#include "libvex_guest_x86.h"

#include "main_util.h"
#include "main_globals.h"
#include "guest_generic_bb_to_IR.h"
#include "guest_generic_x87.h"
#include "guest_x86_defs.h"

/*------------------------------------------------------------*/
/*--- Globals                                              ---*/
/*------------------------------------------------------------*/

/* These are set at the start of the translation of an insn, right
   down in disInstr_X86, so that we don't have to pass them around
   endlessly.  They are all constant during the translation of any
   given insn. */

/* We need to know this to do sub-register accesses correctly. */
static VexEndness host_endness;

/* Pointer to the guest code area (points to start of BB, not to the
   insn being processed). */
static const UChar* guest_code;

/* The guest address corresponding to guest_code[0]. */
static Addr32 guest_EIP_bbstart;

static Addr32 guest_CS_bbstart;

/* The guest address for the instruction currently being
   translated. */
static Addr32 guest_EIP_curr_instr;

/* The IRSB* into which we're generating code. */
static IRSB* irsb;

static Bool ignore_seg_mode;

/*------------------------------------------------------------*/
/*--- Debugging output                                     ---*/
/*------------------------------------------------------------*/

#ifndef _MSC_VER
#define DIP(format, args...)           \
   if (vex_traceflags & VEX_TRACE_FE)  \
      vex_printf(format, ## args)

#define DIS(buf, format, args...)      \
   if (vex_traceflags & VEX_TRACE_FE)  \
      vex_sprintf(buf, format, ## args)
#else
#define DIP(format, ...)           \
   printf(format, __VA_ARGS__); \
   if (vex_traceflags & VEX_TRACE_FE)  \
      vex_printf(format, __VA_ARGS__)

#define DIS(buf, format, ...)      \
   sprintf(buf, format, __VA_ARGS__); \
   if (vex_traceflags & VEX_TRACE_FE)  \
      vex_sprintf(buf, format, __VA_ARGS__)
#endif

#define UNINITALIZED_SREG (0x80000000)
#define EXPLICIT_BIT (0x80)

#define IS_EXPLICIT_BIT_SET(sreg) (0x80 & sreg)

/*------------------------------------------------------------*/
/*--- Offsets of various parts of the x86 guest state.     ---*/
/*------------------------------------------------------------*/

#define OFFB_EAX       offsetof(VexGuestX86State,guest_EAX)
#define OFFB_EBX       offsetof(VexGuestX86State,guest_EBX)
#define OFFB_ECX       offsetof(VexGuestX86State,guest_ECX)
#define OFFB_EDX       offsetof(VexGuestX86State,guest_EDX)
#define OFFB_ESP       offsetof(VexGuestX86State,guest_ESP)
#define OFFB_EBP       offsetof(VexGuestX86State,guest_EBP)
#define OFFB_ESI       offsetof(VexGuestX86State,guest_ESI)
#define OFFB_EDI       offsetof(VexGuestX86State,guest_EDI)

#define OFFB_EIP       offsetof(VexGuestX86State,guest_EIP)

#define OFFB_CC_OP     offsetof(VexGuestX86State,guest_CC_OP)
#define OFFB_CC_DEP1   offsetof(VexGuestX86State,guest_CC_DEP1)
#define OFFB_CC_DEP2   offsetof(VexGuestX86State,guest_CC_DEP2)
#define OFFB_CC_NDEP   offsetof(VexGuestX86State,guest_CC_NDEP)

#define OFFB_FPREGS    offsetof(VexGuestX86State,guest_FPREG[0])
#define OFFB_FPTAGS    offsetof(VexGuestX86State,guest_FPTAG[0])
#define OFFB_DFLAG     offsetof(VexGuestX86State,guest_DFLAG)
#define OFFB_IDFLAG    offsetof(VexGuestX86State,guest_IDFLAG)
#define OFFB_ACFLAG    offsetof(VexGuestX86State,guest_ACFLAG)
#define OFFB_FTOP      offsetof(VexGuestX86State,guest_FTOP)
#define OFFB_FC3210    offsetof(VexGuestX86State,guest_FC3210)
#define OFFB_FPROUND   offsetof(VexGuestX86State,guest_FPROUND)

#define OFFB_CS        offsetof(VexGuestX86State,guest_CS)
#define OFFB_DS        offsetof(VexGuestX86State,guest_DS)
#define OFFB_ES        offsetof(VexGuestX86State,guest_ES)
#define OFFB_FS        offsetof(VexGuestX86State,guest_FS)
#define OFFB_GS        offsetof(VexGuestX86State,guest_GS)
#define OFFB_SS        offsetof(VexGuestX86State,guest_SS)
#define OFFB_LDT       offsetof(VexGuestX86State,guest_LDT)
#define OFFB_GDT       offsetof(VexGuestX86State,guest_GDT)

#define OFFB_SSEROUND  offsetof(VexGuestX86State,guest_SSEROUND)
#define OFFB_XMM0      offsetof(VexGuestX86State,guest_XMM0)
#define OFFB_XMM1      offsetof(VexGuestX86State,guest_XMM1)
#define OFFB_XMM2      offsetof(VexGuestX86State,guest_XMM2)
#define OFFB_XMM3      offsetof(VexGuestX86State,guest_XMM3)
#define OFFB_XMM4      offsetof(VexGuestX86State,guest_XMM4)
#define OFFB_XMM5      offsetof(VexGuestX86State,guest_XMM5)
#define OFFB_XMM6      offsetof(VexGuestX86State,guest_XMM6)
#define OFFB_XMM7      offsetof(VexGuestX86State,guest_XMM7)

#define OFFB_EMNOTE    offsetof(VexGuestX86State,guest_EMNOTE)

#define OFFB_CMSTART   offsetof(VexGuestX86State,guest_CMSTART)
#define OFFB_CMLEN     offsetof(VexGuestX86State,guest_CMLEN)
#define OFFB_NRADDR    offsetof(VexGuestX86State,guest_NRADDR)

#define OFFB_IP_AT_SYSCALL offsetof(VexGuestX86State,guest_IP_AT_SYSCALL)


/*------------------------------------------------------------*/
/*--- Helper bits and pieces for deconstructing the        ---*/
/*--- x86 insn stream.                                     ---*/
/*------------------------------------------------------------*/

/* This is the Intel register encoding -- integer regs. */
#define R_EAX 0
#define R_ECX 1
#define R_EDX 2
#define R_EBX 3
#define R_ESP 4
#define R_EBP 5
#define R_ESI 6
#define R_EDI 7

#define R_AL (0+R_EAX)
#define R_AH (4+R_EAX)

/* This is the Intel register encoding -- segment regs. */
#define R_ES 0
#define R_CS 1
#define R_SS 2
#define R_DS 3
#define R_FS 4
#define R_GS 5
#define UNDEFINED_SEG 255

/* Add a statement to the list held by "irbb". */
static void stmt ( IRStmt* st )
{
   addStmtToIRSB( irsb, st );
}

/* Generate a new temporary of the given type. */
static IRTemp newTemp ( IRType ty )
{
   vassert(isPlausibleIRType(ty));
   return newIRTemp( irsb->tyenv, ty );
}

/* Various simple conversions */

static UInt extend_s_8to32( UInt x )
{
   return (UInt)((Int)(x << 24) >> 24);
}

static UInt extend_s_16to32 ( UInt x )
{
  return (UInt)((Int)(x << 16) >> 16);
}

/* Fetch a byte from the guest insn stream. */
static UChar getIByte ( Int delta )
{
   return guest_code[delta];
}

/* Extract the reg field from a modRM byte. */
static Int gregOfRM ( UChar mod_reg_rm )
{
   return (Int)( (mod_reg_rm >> 3) & 7 );
}

/* Figure out whether the mod and rm parts of a modRM byte refer to a
   register or memory.  If so, the byte will have the form 11XXXYYY,
   where YYY is the register number. */
static Bool epartIsReg ( UChar mod_reg_rm )
{
   return toBool(0xC0 == (mod_reg_rm & 0xC0));
}

/* ... and extract the register number ... */
static Int eregOfRM ( UChar mod_reg_rm )
{
   return (Int)(mod_reg_rm & 0x7);
}

/* Get a 8/16/32-bit unsigned value out of the insn stream. */

static UChar getUChar ( Int delta )
{
   UChar v = guest_code[delta+0];
   return toUChar(v);
}

static UInt getUDisp16 ( Int delta )
{
   UInt v = guest_code[delta+1]; v <<= 8;
   v |= guest_code[delta+0];
   return v & 0xFFFF;
}

static UInt getUDisp32 ( Int delta )
{
   UInt v = guest_code[delta+3]; v <<= 8;
   v |= guest_code[delta+2]; v <<= 8;
   v |= guest_code[delta+1]; v <<= 8;
   v |= guest_code[delta+0];
   return v;
}

static UInt getUDisp ( Int size, Int delta )
{
   switch (size) {
      case 4: return getUDisp32(delta);
      case 2: return getUDisp16(delta);
      case 1: return (UInt)getUChar(delta);
      default: vpanic("getUDisp(x86)");
   }
   return 0; /*notreached*/
}


/* Get a byte value out of the insn stream and sign-extend to 32
   bits. */
static UInt getSDisp8 ( Int delta )
{
   return extend_s_8to32( (UInt) (guest_code[delta]) );
}

static UInt getSDisp16 ( Int delta0 )
{
   const UChar* eip = &guest_code[delta0];
   UInt d = *eip++;
   d |= ((*eip++) << 8);
   return extend_s_16to32(d);
}

static UInt getSDisp ( Int size, Int delta )
{
   switch (size) {
      case 4: return getUDisp32(delta);
      case 2: return getSDisp16(delta);
      case 1: return getSDisp8(delta);
      default: vpanic("getSDisp(x86)");
  }
  return 0; /*notreached*/
}


/*------------------------------------------------------------*/
/*--- Helpers for constructing IR.                         ---*/
/*------------------------------------------------------------*/

/* Create a 1/2/4 byte read of an x86 integer registers.  For 16/8 bit
   register references, we need to take the host endianness into
   account.  Supplied value is 0 .. 7 and in the Intel instruction
   encoding. */

static IRType szToITy ( Int n )
{
   switch (n) {
      case 1: return Ity_I8;
      case 2: return Ity_I16;
      case 4: return Ity_I32;
      default: vpanic("szToITy(x86)");
   }
}

/* On a little-endian host, less significant bits of the guest
   registers are at lower addresses.  Therefore, if a reference to a
   register low half has the safe guest state offset as a reference to
   the full register.
*/
static Int integerGuestRegOffset ( Int sz, UInt archreg )
{
   vassert(archreg < 8);

   /* Correct for little-endian host only. */
   vassert(host_endness == VexEndnessLE);

   if (sz == 4 || sz == 2 || (sz == 1 && archreg < 4)) {
      switch (archreg) {
         case R_EAX: return OFFB_EAX;
         case R_EBX: return OFFB_EBX;
         case R_ECX: return OFFB_ECX;
         case R_EDX: return OFFB_EDX;
         case R_ESI: return OFFB_ESI;
         case R_EDI: return OFFB_EDI;
         case R_ESP: return OFFB_ESP;
         case R_EBP: return OFFB_EBP;
         default: vpanic("integerGuestRegOffset(x86,le)(4,2)");
      }
   }

   vassert(archreg >= 4 && archreg < 8 && sz == 1);
   switch (archreg-4) {
      case R_EAX: return 1+ OFFB_EAX;
      case R_EBX: return 1+ OFFB_EBX;
      case R_ECX: return 1+ OFFB_ECX;
      case R_EDX: return 1+ OFFB_EDX;
      default: vpanic("integerGuestRegOffset(x86,le)(1h)");
   }

   /* NOTREACHED */
   vpanic("integerGuestRegOffset(x86,le)");
}

static Int segmentGuestRegOffset ( UInt sreg )
{
   sreg = sreg & ~EXPLICIT_BIT;
   switch (sreg) {
      case R_ES: return OFFB_ES;
      case R_CS: return OFFB_CS;
      case R_SS: return OFFB_SS;
      case R_DS: return OFFB_DS;
      default: vpanic("segmentGuestRegOffset(8086)");
   }
}

static IRExpr* getIReg ( Int sz, UInt archreg )
{
   vassert(sz == 1 || sz == 2 || sz == 4);
   vassert(archreg < 8);
   return IRExpr_Get( integerGuestRegOffset(sz,archreg),
                      szToITy(sz) );
}

/* Ditto, but write to a reg instead. */
static void putIReg ( Int sz, UInt archreg, IRExpr* e )
{
   IRType ty = typeOfIRExpr(irsb->tyenv, e);
   switch (sz) {
      case 1: vassert(ty == Ity_I8); break;
      case 2: vassert(ty == Ity_I16); break;
      case 4: vassert(ty == Ity_I32); break;
      default: vpanic("putIReg(x86)");
   }
   vassert(archreg < 8);
   stmt( IRStmt_Put(integerGuestRegOffset(sz,archreg), e) );
}

static IRExpr* getSReg ( UInt sreg )
{
   return IRExpr_Get( segmentGuestRegOffset(sreg), Ity_I16 );
}

static void putSReg ( UInt sreg, IRExpr* e )
{
   vassert(typeOfIRExpr(irsb->tyenv,e) == Ity_I16);
   stmt( IRStmt_Put( segmentGuestRegOffset(sreg), e ) );
}

static void assign ( IRTemp dst, IRExpr* e )
{
   stmt( IRStmt_WrTmp(dst, e) );
}

static void storeLE ( IRExpr* addr, IRExpr* data )
{
   stmt( IRStmt_Store(Iend_LE, addr, data) );
}

static IRExpr* unop ( IROp op, IRExpr* a )
{
   return IRExpr_Unop(op, a);
}

static IRExpr* binop ( IROp op, IRExpr* a1, IRExpr* a2 )
{
   return IRExpr_Binop(op, a1, a2);
}

static IRExpr* triop ( IROp op, IRExpr* a1, IRExpr* a2, IRExpr* a3 )
{
   return IRExpr_Triop(op, a1, a2, a3);
}

static IRExpr* mkexpr ( IRTemp tmp )
{
   return IRExpr_RdTmp(tmp);
}

static IRExpr* mkU8 ( UInt i )
{
   vassert(i < 256);
   return IRExpr_Const(IRConst_U8( (UChar)i ));
}

static IRExpr* mkU16 ( UInt i )
{
   vassert(i < 65536);
   return IRExpr_Const(IRConst_U16( (UShort)i ));
}

static IRExpr* mkU32 ( UInt i )
{
   return IRExpr_Const(IRConst_U32(i));
}

static IRExpr* mkU64 ( ULong i )
{
   return IRExpr_Const(IRConst_U64(i));
}

static IRExpr* mkU ( IRType ty, UInt i )
{
   if (ty == Ity_I8)  return mkU8(i);
   if (ty == Ity_I16) return mkU16(i);
   if (ty == Ity_I32) return mkU32(i);
   /* If this panics, it usually means you passed a size (1,2,4)
      value as the IRType, rather than a real IRType. */
   vpanic("mkU(x86)");
}

static IRExpr* mkV128 ( UShort mask )
{
   return IRExpr_Const(IRConst_V128(mask));
}

static IRExpr* loadLE ( IRType ty, IRExpr* addr )
{
   return IRExpr_Load(Iend_LE, ty, addr);
}

static IROp mkSizedOp ( IRType ty, IROp op8 )
{
   Int adj;
   vassert(ty == Ity_I8 || ty == Ity_I16 || ty == Ity_I32);
   vassert(op8 == Iop_Add8 || op8 == Iop_Sub8 
           || op8 == Iop_Mul8 
           || op8 == Iop_Or8 || op8 == Iop_And8 || op8 == Iop_Xor8
           || op8 == Iop_Shl8 || op8 == Iop_Shr8 || op8 == Iop_Sar8
           || op8 == Iop_CmpEQ8 || op8 == Iop_CmpNE8
           || op8 == Iop_CasCmpNE8
           || op8 == Iop_ExpCmpNE8
           || op8 == Iop_Not8);
   adj = ty==Ity_I8 ? 0 : (ty==Ity_I16 ? 1 : 2);
   return adj + op8;
}

static IROp mkWidenOp ( Int szSmall, Int szBig, Bool signd )
{
   if (szSmall == 1 && szBig == 4) {
      return signd ? Iop_8Sto32 : Iop_8Uto32;
   }
   if (szSmall == 1 && szBig == 2) {
      return signd ? Iop_8Sto16 : Iop_8Uto16;
   }
   if (szSmall == 2 && szBig == 4) {
      return signd ? Iop_16Sto32 : Iop_16Uto32;
   }
   vpanic("mkWidenOp(x86,guest)");
}

static IRExpr* mkAnd1 ( IRExpr* x, IRExpr* y )
{
   vassert(typeOfIRExpr(irsb->tyenv,x) == Ity_I1);
   vassert(typeOfIRExpr(irsb->tyenv,y) == Ity_I1);
   return unop(Iop_32to1, 
               binop(Iop_And32, 
                     unop(Iop_1Uto32,x), 
                     unop(Iop_1Uto32,y)));
}

/* Generate a compare-and-swap operation, operating on memory at
   'addr'.  The expected value is 'expVal' and the new value is
   'newVal'.  If the operation fails, then transfer control (with a
   no-redir jump (XXX no -- see comment at top of this file)) to
   'restart_point', which is presumably the address of the guest
   instruction again -- retrying, essentially. */
static void casLE ( IRExpr* addr, IRExpr* expVal, IRExpr* newVal,
                    Addr32 restart_point )
{
   IRCAS* cas;
   IRType tyE    = typeOfIRExpr(irsb->tyenv, expVal);
   IRType tyN    = typeOfIRExpr(irsb->tyenv, newVal);
   IRTemp oldTmp = newTemp(tyE);
   IRTemp expTmp = newTemp(tyE);
   vassert(tyE == tyN);
   vassert(tyE == Ity_I32 || tyE == Ity_I16 || tyE == Ity_I8);
   assign(expTmp, expVal);
   cas = mkIRCAS( IRTemp_INVALID, oldTmp, Iend_LE, addr, 
                  NULL, mkexpr(expTmp), NULL, newVal );
   stmt( IRStmt_CAS(cas) );
   stmt( IRStmt_Exit(
            binop( mkSizedOp(tyE,Iop_CasCmpNE8),
                   mkexpr(oldTmp), mkexpr(expTmp) ),
            Ijk_Boring, /*Ijk_NoRedir*/
            IRConst_U32( restart_point ),
            OFFB_EIP
         ));
}




/*------------------------------------------------------------*/
/*--- Helpers for %eflags.                                 ---*/
/*------------------------------------------------------------*/

/* -------------- Evaluating the flags-thunk. -------------- */

/* Build IR to calculate all the eflags from stored
   CC_OP/CC_DEP1/CC_DEP2/CC_NDEP.  Returns an expression ::
   Ity_I32. */
static IRExpr* mk_x86g_calculate_eflags_all ( void )
{
   IRExpr** args
      = mkIRExprVec_4( IRExpr_Get(OFFB_CC_OP,   Ity_I32),
                       IRExpr_Get(OFFB_CC_DEP1, Ity_I32),
                       IRExpr_Get(OFFB_CC_DEP2, Ity_I32),
                       IRExpr_Get(OFFB_CC_NDEP, Ity_I32) );
   IRExpr* call
      = mkIRExprCCall(
           Ity_I32,
           0/*regparm*/, 
           "x86g_calculate_eflags_all", &x86g_calculate_eflags_all,
           args
        );
   /* Exclude OP and NDEP from definedness checking.  We're only
      interested in DEP1 and DEP2. */
   call->Iex.CCall.cee->mcx_mask = (1<<0) | (1<<3);
   return call;
}

/* Build IR to calculate some particular condition from stored
   CC_OP/CC_DEP1/CC_DEP2/CC_NDEP.  Returns an expression ::
   Ity_Bit. */
static IRExpr* mk_x86g_calculate_condition ( X86Condcode cond )
{
   IRExpr** args
      = mkIRExprVec_5( mkU32(cond),
                       IRExpr_Get(OFFB_CC_OP,  Ity_I32),
                       IRExpr_Get(OFFB_CC_DEP1, Ity_I32),
                       IRExpr_Get(OFFB_CC_DEP2, Ity_I32),
                       IRExpr_Get(OFFB_CC_NDEP, Ity_I32) );
   IRExpr* call
      = mkIRExprCCall(
           Ity_I32,
           0/*regparm*/, 
           "x86g_calculate_condition", &x86g_calculate_condition,
           args
        );
   /* Exclude the requested condition, OP and NDEP from definedness
      checking.  We're only interested in DEP1 and DEP2. */
   call->Iex.CCall.cee->mcx_mask = (1<<0) | (1<<1) | (1<<4);
   return unop(Iop_32to1, call);
}

/* Build IR to calculate just the carry flag from stored
   CC_OP/CC_DEP1/CC_DEP2/CC_NDEP.  Returns an expression :: Ity_I32. */
static IRExpr* mk_x86g_calculate_eflags_c ( void )
{
   IRExpr** args
      = mkIRExprVec_4( IRExpr_Get(OFFB_CC_OP,   Ity_I32),
                       IRExpr_Get(OFFB_CC_DEP1, Ity_I32),
                       IRExpr_Get(OFFB_CC_DEP2, Ity_I32),
                       IRExpr_Get(OFFB_CC_NDEP, Ity_I32) );
   IRExpr* call
      = mkIRExprCCall(
           Ity_I32,
           3/*regparm*/, 
           "x86g_calculate_eflags_c", &x86g_calculate_eflags_c,
           args
        );
   /* Exclude OP and NDEP from definedness checking.  We're only
      interested in DEP1 and DEP2. */
   call->Iex.CCall.cee->mcx_mask = (1<<0) | (1<<3);
   return call;
}


/* -------------- Building the flags-thunk. -------------- */

/* The machinery in this section builds the flag-thunk following a
   flag-setting operation.  Hence the various setFlags_* functions.
*/

static Bool isAddSub ( IROp op8 )
{
   return toBool(op8 == Iop_Add8 || op8 == Iop_Sub8);
}

static Bool isLogic ( IROp op8 )
{
   return toBool(op8 == Iop_And8 || op8 == Iop_Or8 || op8 == Iop_Xor8);
}

/* U-widen 8/16/32 bit int expr to 32. */
static IRExpr* widenUto32 ( IRExpr* e )
{
   switch (typeOfIRExpr(irsb->tyenv,e)) {
      case Ity_I32: return e;
      case Ity_I16: return unop(Iop_16Uto32,e);
      case Ity_I8:  return unop(Iop_8Uto32,e);
      default: vpanic("widenUto32");
   }
}

/* S-widen 8/16/32 bit int expr to 32. */
static IRExpr* widenSto32 ( IRExpr* e )
{
   switch (typeOfIRExpr(irsb->tyenv,e)) {
      case Ity_I32: return e;
      case Ity_I16: return unop(Iop_16Sto32,e);
      case Ity_I8:  return unop(Iop_8Sto32,e);
      default: vpanic("widenSto32");
   }
}

/* Narrow 8/16/32 bit int expr to 8/16/32.  Clearly only some
   of these combinations make sense. */
static IRExpr* narrowTo ( IRType dst_ty, IRExpr* e )
{
   IRType src_ty = typeOfIRExpr(irsb->tyenv,e);
   if (src_ty == dst_ty)
      return e;
   if (src_ty == Ity_I32 && dst_ty == Ity_I16)
      return unop(Iop_32to16, e);
   if (src_ty == Ity_I32 && dst_ty == Ity_I8)
      return unop(Iop_32to8, e);

   vex_printf("\nsrc, dst tys are: ");
   ppIRType(src_ty);
   vex_printf(", ");
   ppIRType(dst_ty);
   vex_printf("\n");
   vpanic("narrowTo(x86)");
}


/* Set the flags thunk OP, DEP1 and DEP2 fields.  The supplied op is
   auto-sized up to the real op. */

static 
void setFlags_DEP1_DEP2 ( IROp op8, IRTemp dep1, IRTemp dep2, IRType ty )
{
   Int ccOp = ty==Ity_I8 ? 0 : (ty==Ity_I16 ? 1 : 2);

   vassert(ty == Ity_I8 || ty == Ity_I16 || ty == Ity_I32);

   switch (op8) {
      case Iop_Add8: ccOp += X86G_CC_OP_ADDB;   break;
      case Iop_Sub8: ccOp += X86G_CC_OP_SUBB;   break;
      default:       ppIROp(op8);
                     vpanic("setFlags_DEP1_DEP2(x86)");
   }
   stmt( IRStmt_Put( OFFB_CC_OP,   mkU32(ccOp)) );
   stmt( IRStmt_Put( OFFB_CC_DEP1, widenUto32(mkexpr(dep1))) );
   stmt( IRStmt_Put( OFFB_CC_DEP2, widenUto32(mkexpr(dep2))) );
   /* Set NDEP even though it isn't used.  This makes redundant-PUT
      elimination of previous stores to this field work better. */
   stmt( IRStmt_Put( OFFB_CC_NDEP, mkU32(0) ));
}


/* Set the OP and DEP1 fields only, and write zero to DEP2. */

static 
void setFlags_DEP1 ( IROp op8, IRTemp dep1, IRType ty )
{
   Int ccOp = ty==Ity_I8 ? 0 : (ty==Ity_I16 ? 1 : 2);

   vassert(ty == Ity_I8 || ty == Ity_I16 || ty == Ity_I32);

   switch (op8) {
      case Iop_Or8:
      case Iop_And8:
      case Iop_Xor8: ccOp += X86G_CC_OP_LOGICB; break;
      default:       ppIROp(op8);
                     vpanic("setFlags_DEP1(x86)");
   }
   stmt( IRStmt_Put( OFFB_CC_OP,   mkU32(ccOp)) );
   stmt( IRStmt_Put( OFFB_CC_DEP1, widenUto32(mkexpr(dep1))) );
   stmt( IRStmt_Put( OFFB_CC_DEP2, mkU32(0)) );
   /* Set NDEP even though it isn't used.  This makes redundant-PUT
      elimination of previous stores to this field work better. */
   stmt( IRStmt_Put( OFFB_CC_NDEP, mkU32(0) ));
}


/* For shift operations, we put in the result and the undershifted
   result.  Except if the shift amount is zero, the thunk is left
   unchanged. */

static void setFlags_DEP1_DEP2_shift ( IROp    op32,
                                       IRTemp  res,
                                       IRTemp  resUS,
                                       IRType  ty,
                                       IRTemp  guard )
{
   Int ccOp = ty==Ity_I8 ? 2 : (ty==Ity_I16 ? 1 : 0);

   vassert(ty == Ity_I8 || ty == Ity_I16 || ty == Ity_I32);
   vassert(guard);

   /* Both kinds of right shifts are handled by the same thunk
      operation. */
   switch (op32) {
      case Iop_Shr32:
      case Iop_Sar32: ccOp = X86G_CC_OP_SHRL - ccOp; break;
      case Iop_Shl32: ccOp = X86G_CC_OP_SHLL - ccOp; break;
      default:        ppIROp(op32);
                      vpanic("setFlags_DEP1_DEP2_shift(x86)");
   }

   /* guard :: Ity_I8.  We need to convert it to I1. */
   IRTemp guardB = newTemp(Ity_I1);
   assign( guardB, binop(Iop_CmpNE8, mkexpr(guard), mkU8(0)) );

   /* DEP1 contains the result, DEP2 contains the undershifted value. */
   stmt( IRStmt_Put( OFFB_CC_OP,
                     IRExpr_ITE( mkexpr(guardB),
                                 mkU32(ccOp),
                                 IRExpr_Get(OFFB_CC_OP,Ity_I32) ) ));
   stmt( IRStmt_Put( OFFB_CC_DEP1,
                     IRExpr_ITE( mkexpr(guardB),
                                 widenUto32(mkexpr(res)),
                                 IRExpr_Get(OFFB_CC_DEP1,Ity_I32) ) ));
   stmt( IRStmt_Put( OFFB_CC_DEP2, 
                     IRExpr_ITE( mkexpr(guardB),
                                 widenUto32(mkexpr(resUS)),
                                 IRExpr_Get(OFFB_CC_DEP2,Ity_I32) ) ));
   /* Set NDEP even though it isn't used.  This makes redundant-PUT
      elimination of previous stores to this field work better. */
   stmt( IRStmt_Put( OFFB_CC_NDEP,
                     IRExpr_ITE( mkexpr(guardB),
                                 mkU32(0),
                                 IRExpr_Get(OFFB_CC_NDEP,Ity_I32) ) ));
}


/* For the inc/dec case, we store in DEP1 the result value and in NDEP
   the former value of the carry flag, which unfortunately we have to
   compute. */

static void setFlags_INC_DEC ( Bool inc, IRTemp res, IRType ty )
{
   Int ccOp = inc ? X86G_CC_OP_INCB : X86G_CC_OP_DECB;
   
   ccOp += ty==Ity_I8 ? 0 : (ty==Ity_I16 ? 1 : 2);
   vassert(ty == Ity_I8 || ty == Ity_I16 || ty == Ity_I32);

   /* This has to come first, because calculating the C flag 
      may require reading all four thunk fields. */
   stmt( IRStmt_Put( OFFB_CC_NDEP, mk_x86g_calculate_eflags_c()) );
   stmt( IRStmt_Put( OFFB_CC_OP,   mkU32(ccOp)) );
   stmt( IRStmt_Put( OFFB_CC_DEP1, widenUto32(mkexpr(res))) );
   stmt( IRStmt_Put( OFFB_CC_DEP2, mkU32(0)) );
}


/* Multiplies are pretty much like add and sub: DEP1 and DEP2 hold the
   two arguments. */

static
void setFlags_MUL ( IRType ty, IRTemp arg1, IRTemp arg2, UInt base_op )
{
   switch (ty) {
      case Ity_I8:
         stmt( IRStmt_Put( OFFB_CC_OP, mkU32(base_op+0) ) );
         break;
      case Ity_I16:
         stmt( IRStmt_Put( OFFB_CC_OP, mkU32(base_op+1) ) );
         break;
      case Ity_I32:
         stmt( IRStmt_Put( OFFB_CC_OP, mkU32(base_op+2) ) );
         break;
      default:
         vpanic("setFlags_MUL(x86)");
   }
   stmt( IRStmt_Put( OFFB_CC_DEP1, widenUto32(mkexpr(arg1)) ));
   stmt( IRStmt_Put( OFFB_CC_DEP2, widenUto32(mkexpr(arg2)) ));
   /* Set NDEP even though it isn't used.  This makes redundant-PUT
      elimination of previous stores to this field work better. */
   stmt( IRStmt_Put( OFFB_CC_NDEP, mkU32(0) ));
}


/* --- Set the emulation-warning pseudo-register. --- */

static void put_emwarn ( IRExpr* e /* :: Ity_I32 */ )
{
   vassert(typeOfIRExpr(irsb->tyenv, e) == Ity_I32);
   stmt( IRStmt_Put( OFFB_EMNOTE, e ) );
}

/* Generate IR to set the guest %EFLAGS from the pushfl-format image
   in the given 32-bit temporary.  The flags that are set are: O S Z A
   C P D ID AC.

   In all cases, code to set AC is generated.  However, VEX actually
   ignores the AC value and so can optionally emit an emulation
   warning when it is enabled.  In this routine, an emulation warning
   is only emitted if emit_AC_emwarn is True, in which case
   next_insn_EIP must be correct (this allows for correct code
   generation for popfl/popfw).  If emit_AC_emwarn is False,
   next_insn_EIP is unimportant (this allows for easy if kludgey code
   generation for IRET.) */

static 
void set_EFLAGS_from_value ( IRTemp t1, 
                             Bool   emit_AC_emwarn,
                             Addr32 next_insn_EIP )
{
   vassert(typeOfIRTemp(irsb->tyenv,t1) == Ity_I32);

   /* t1 is the flag word.  Mask out everything except OSZACP and set
      the flags thunk to X86G_CC_OP_COPY. */
   stmt( IRStmt_Put( OFFB_CC_OP,   mkU32(X86G_CC_OP_COPY) ));
   stmt( IRStmt_Put( OFFB_CC_DEP2, mkU32(0) ));
   stmt( IRStmt_Put( OFFB_CC_DEP1, 
                     binop(Iop_And32,
                           mkexpr(t1), 
                           mkU32( X86G_CC_MASK_C | X86G_CC_MASK_P 
                                  | X86G_CC_MASK_A | X86G_CC_MASK_Z 
                                  | X86G_CC_MASK_S| X86G_CC_MASK_O )
                          )
                    )
       );
   /* Set NDEP even though it isn't used.  This makes redundant-PUT
      elimination of previous stores to this field work better. */
   stmt( IRStmt_Put( OFFB_CC_NDEP, mkU32(0) ));

   /* Also need to set the D flag, which is held in bit 10 of t1.
      If zero, put 1 in OFFB_DFLAG, else -1 in OFFB_DFLAG. */
   stmt( IRStmt_Put( 
            OFFB_DFLAG,
            IRExpr_ITE( 
               unop(Iop_32to1,
                    binop(Iop_And32, 
                          binop(Iop_Shr32, mkexpr(t1), mkU8(10)), 
                          mkU32(1))),
               mkU32(0xFFFFFFFF),
               mkU32(1)))
       );

   /* Set the ID flag */
   stmt( IRStmt_Put( 
            OFFB_IDFLAG,
            IRExpr_ITE( 
               unop(Iop_32to1,
                    binop(Iop_And32, 
                          binop(Iop_Shr32, mkexpr(t1), mkU8(21)), 
                          mkU32(1))),
               mkU32(1),
               mkU32(0)))
       );

   /* And set the AC flag.  If setting it 1 to, possibly emit an
      emulation warning. */
   stmt( IRStmt_Put( 
            OFFB_ACFLAG,
            IRExpr_ITE( 
               unop(Iop_32to1,
                    binop(Iop_And32, 
                          binop(Iop_Shr32, mkexpr(t1), mkU8(18)), 
                          mkU32(1))),
               mkU32(1),
               mkU32(0)))
       );

   if (emit_AC_emwarn) {
      put_emwarn( mkU32(EmWarn_X86_acFlag) );
      stmt( 
         IRStmt_Exit(
            binop( Iop_CmpNE32, 
                   binop(Iop_And32, mkexpr(t1), mkU32(1<<18)), 
                   mkU32(0) ),
            Ijk_EmWarn,
            IRConst_U32( next_insn_EIP ),
            OFFB_EIP
         )
      );
   }
}

#define is_bit_set(var,pos) ((var & (1<<pos))>>pos)
#define SEG_SHIFT (4)

static
UInt fix_ip(UInt Eip){
   UInt ip = Eip - (guest_CS_bbstart << SEG_SHIFT);
   vassert((Int)ip >= 0);
   ip &= 0xffff;

   return (ip + (guest_CS_bbstart << SEG_SHIFT));
}

static IRExpr* realAddr( IRExpr* segaddr ,IRExpr* addr )
{
   return binop(Iop_Add32, addr, binop(Iop_Shl32, unop(Iop_16Uto32,segaddr), mkU8(SEG_SHIFT)));
}

static IRExpr* loadRealLE ( IRType ty, Int sreg , IRExpr* addr)
{
   if(( !IS_EXPLICIT_BIT_SET(sreg) && ignore_seg_mode) || sreg == UNDEFINED_SEG){
      return loadLE(ty, addr);
   }
   return loadLE( ty, realAddr(getSReg(sreg), addr ));
}

static void storeRealLE ( IRExpr* addr,Int sreg,  IRExpr* data)
{
   if((!IS_EXPLICIT_BIT_SET(sreg) && ignore_seg_mode) || sreg == UNDEFINED_SEG){
      storeLE(addr, data);
      return;
   }
   storeLE(realAddr(getSReg(sreg), addr),data);
}

/* -------------- Condition codes. -------------- */

/* Condition codes, using the Intel encoding.  */

static const HChar* name_X86Condcode ( X86Condcode cond )
{
   switch (cond) {
      case X86CondO:      return "o";
      case X86CondNO:     return "no";
      case X86CondB:      return "b";
      case X86CondNB:     return "nb";
      case X86CondZ:      return "z";
      case X86CondNZ:     return "nz";
      case X86CondBE:     return "be";
      case X86CondNBE:    return "nbe";
      case X86CondS:      return "s";
      case X86CondNS:     return "ns";
      case X86CondP:      return "p";
      case X86CondNP:     return "np";
      case X86CondL:      return "l";
      case X86CondNL:     return "nl";
      case X86CondLE:     return "le";
      case X86CondNLE:    return "nle";
      case X86CondAlways: return "ALWAYS";
      default: vpanic("name_X86Condcode");
   }
}

static 
X86Condcode positiveIse_X86Condcode ( X86Condcode  cond,
                                      Bool*        needInvert )
{
   vassert(cond >= X86CondO && cond <= X86CondNLE);
   if (cond & 1) {
      *needInvert = True;
      return cond-1;
   } else {
      *needInvert = False;
      return cond;
   }
}



/* -------------- Helpers for ADD/SUB with carry. -------------- */

/* Given ta1, ta2 and tres, compute tres = ADC(ta1,ta2) and set flags
   appropriately.

   Optionally, generate a store for the 'tres' value.  This can either
   be a normal store, or it can be a cas-with-possible-failure style
   store:

   if taddr is IRTemp_INVALID, then no store is generated.

   if taddr is not IRTemp_INVALID, then a store (using taddr as
   the address) is generated:

     if texpVal is IRTemp_INVALID then a normal store is
     generated, and restart_point must be zero (it is irrelevant).

     if texpVal is not IRTemp_INVALID then a cas-style store is
     generated.  texpVal is the expected value, restart_point
     is the restart point if the store fails, and texpVal must
     have the same type as tres.   
*/
static void helper_ADC ( Int sz,
                         IRTemp tres, IRTemp ta1, IRTemp ta2,
                         /* info about optional store: */
                         IRTemp taddr, IRTemp texpVal, Addr32 restart_point , UChar sorb)
{
   UInt    thunkOp;
   IRType  ty    = szToITy(sz);
   IRTemp  oldc  = newTemp(Ity_I32);
   IRTemp  oldcn = newTemp(ty);
   IROp    plus  = mkSizedOp(ty, Iop_Add8);
   IROp    xor   = mkSizedOp(ty, Iop_Xor8);

   vassert(typeOfIRTemp(irsb->tyenv, tres) == ty);
   vassert(sz == 1 || sz == 2 || sz == 4);
   thunkOp = sz==4 ? X86G_CC_OP_ADCL 
                   : (sz==2 ? X86G_CC_OP_ADCW : X86G_CC_OP_ADCB);

   /* oldc = old carry flag, 0 or 1 */
   assign( oldc,  binop(Iop_And32,
                        mk_x86g_calculate_eflags_c(),
                        mkU32(1)) );

   assign( oldcn, narrowTo(ty, mkexpr(oldc)) );

   assign( tres, binop(plus,
                       binop(plus,mkexpr(ta1),mkexpr(ta2)),
                       mkexpr(oldcn)) );

   /* Possibly generate a store of 'tres' to 'taddr'.  See comment at
      start of this function. */
   if (taddr != IRTemp_INVALID) {
      if (texpVal == IRTemp_INVALID) {
         vassert(restart_point == 0);
         storeRealLE( mkexpr(taddr),sorb, mkexpr(tres) );
      } else {
         vassert(typeOfIRTemp(irsb->tyenv, texpVal) == ty);
         /* .. and hence 'texpVal' has the same type as 'tres'. */
         casLE( mkexpr(taddr),
                mkexpr(texpVal), mkexpr(tres), restart_point );
      }
   }

   stmt( IRStmt_Put( OFFB_CC_OP,   mkU32(thunkOp) ) );
   stmt( IRStmt_Put( OFFB_CC_DEP1, widenUto32(mkexpr(ta1)) ));
   stmt( IRStmt_Put( OFFB_CC_DEP2, widenUto32(binop(xor, mkexpr(ta2), 
                                                         mkexpr(oldcn)) )) );
   stmt( IRStmt_Put( OFFB_CC_NDEP, mkexpr(oldc) ) );
}


/* Given ta1, ta2 and tres, compute tres = SBB(ta1,ta2) and set flags
   appropriately.  As with helper_ADC, possibly generate a store of
   the result -- see comments on helper_ADC for details.
*/
static void helper_SBB ( Int sz,
                         IRTemp tres, IRTemp ta1, IRTemp ta2,
                         /* info about optional store: */
                         IRTemp taddr, IRTemp texpVal, Addr32 restart_point , UChar sorb)
{
   UInt    thunkOp;
   IRType  ty    = szToITy(sz);
   IRTemp  oldc  = newTemp(Ity_I32);
   IRTemp  oldcn = newTemp(ty);
   IROp    minus = mkSizedOp(ty, Iop_Sub8);
   IROp    xor   = mkSizedOp(ty, Iop_Xor8);

   vassert(typeOfIRTemp(irsb->tyenv, tres) == ty);
   vassert(sz == 1 || sz == 2 || sz == 4);
   thunkOp = sz==4 ? X86G_CC_OP_SBBL 
                   : (sz==2 ? X86G_CC_OP_SBBW : X86G_CC_OP_SBBB);

   /* oldc = old carry flag, 0 or 1 */
   assign( oldc, binop(Iop_And32,
                       mk_x86g_calculate_eflags_c(),
                       mkU32(1)) );

   assign( oldcn, narrowTo(ty, mkexpr(oldc)) );

   assign( tres, binop(minus,
                       binop(minus,mkexpr(ta1),mkexpr(ta2)),
                       mkexpr(oldcn)) );

   /* Possibly generate a store of 'tres' to 'taddr'.  See comment at
      start of this function. */
   if (taddr != IRTemp_INVALID) {
      if (texpVal == IRTemp_INVALID) {
         vassert(restart_point == 0);
         storeRealLE( mkexpr(taddr),sorb,  mkexpr(tres) );
      } else {
         vassert(typeOfIRTemp(irsb->tyenv, texpVal) == ty);
         /* .. and hence 'texpVal' has the same type as 'tres'. */
         casLE( mkexpr(taddr),
                mkexpr(texpVal), mkexpr(tres), restart_point );
      }
   }

   stmt( IRStmt_Put( OFFB_CC_OP,   mkU32(thunkOp) ) );
   stmt( IRStmt_Put( OFFB_CC_DEP1, widenUto32(mkexpr(ta1) )) );
   stmt( IRStmt_Put( OFFB_CC_DEP2, widenUto32(binop(xor, mkexpr(ta2), 
                                                         mkexpr(oldcn)) )) );
   stmt( IRStmt_Put( OFFB_CC_NDEP, mkexpr(oldc) ) );
}

/* -------------- Helpers for disassembly printing. -------------- */

static const HChar* nameGrp1 ( Int opc_aux )
{
   static const HChar* grp1_names[8] 
     = { "add", "or", "adc", "sbb", "and", "sub", "xor", "cmp" };
   if (opc_aux < 0 || opc_aux > 7) vpanic("nameGrp1(x86)");
   return grp1_names[opc_aux];
}

static const HChar* nameGrp2 ( Int opc_aux )
{
   static const HChar* grp2_names[8] 
     = { "rol", "ror", "rcl", "rcr", "shl", "shr", "shl", "sar" };
   if (opc_aux < 0 || opc_aux > 7) vpanic("nameGrp2(x86)");
   return grp2_names[opc_aux];
}

static const HChar* nameGrp4 ( Int opc_aux )
{
   static const HChar* grp4_names[8] 
     = { "inc", "dec", "???", "???", "???", "???", "???", "???" };
   if (opc_aux < 0 || opc_aux > 1) vpanic("nameGrp4(x86)");
   return grp4_names[opc_aux];
}

static const HChar* nameGrp5 ( Int opc_aux )
{
   static const HChar* grp5_names[8] 
     = { "inc", "dec", "call*", "call*", "jmp*", "jmp*", "push", "???" };
   if (opc_aux < 0 || opc_aux > 6) vpanic("nameGrp5(x86)");
   return grp5_names[opc_aux];
}

static const HChar* nameGrp8 ( Int opc_aux )
{
   static const HChar* grp8_names[8] 
     = { "???", "???", "???", "???", "bt", "bts", "btr", "btc" };
   if (opc_aux < 4 || opc_aux > 7) vpanic("nameGrp8(x86)");
   return grp8_names[opc_aux];
}

static const HChar* nameIReg ( Int size, Int reg )
{
   static const HChar* ireg32_names[8] 
     = { "%eax", "%ecx", "%edx", "%ebx", 
         "%esp", "%ebp", "%esi", "%edi" };
   static const HChar* ireg16_names[8] 
     = { "%ax", "%cx", "%dx", "%bx", "%sp", "%bp", "%si", "%di" };
   static const HChar* ireg8_names[8] 
     = { "%al", "%cl", "%dl", "%bl", 
         "%ah{sp}", "%ch{bp}", "%dh{si}", "%bh{di}" };
   if (reg < 0 || reg > 7) goto bad;
   switch (size) {
      case 4: return ireg32_names[reg];
      case 2: return ireg16_names[reg];
      case 1: return ireg8_names[reg];
   }
  bad:
   vpanic("nameIReg(X86)");
   return NULL; /*notreached*/
}

static const HChar* nameSReg ( UInt sreg )
{
   switch (sreg) {
      case R_ES: return "%es";
      case R_CS: return "%cs";
      case R_SS: return "%ss";
      case R_DS: return "%ds";
      case R_FS: return "%fs";
      case R_GS: return "%gs";
      default: vpanic("nameSReg(x86)");
   }
}

static const HChar* nameMMXReg ( Int mmxreg )
{
   static const HChar* mmx_names[8] 
     = { "%mm0", "%mm1", "%mm2", "%mm3", "%mm4", "%mm5", "%mm6", "%mm7" };
   if (mmxreg < 0 || mmxreg > 7) vpanic("nameMMXReg(x86,guest)");
   return mmx_names[mmxreg];
}

static const HChar* nameXMMReg ( Int xmmreg )
{
   static const HChar* xmm_names[8] 
     = { "%xmm0", "%xmm1", "%xmm2", "%xmm3", 
         "%xmm4", "%xmm5", "%xmm6", "%xmm7" };
   if (xmmreg < 0 || xmmreg > 7) vpanic("name_of_xmm_reg");
   return xmm_names[xmmreg];
}
 
static const HChar* nameMMXGran ( Int gran )
{
   switch (gran) {
      case 0: return "b";
      case 1: return "w";
      case 2: return "d";
      case 3: return "q";
      default: vpanic("nameMMXGran(x86,guest)");
   }
}

static HChar nameISize ( Int size )
{
   switch (size) {
      case 4: return 'l';
      case 2: return 'w';
      case 1: return 'b';
      default: vpanic("nameISize(x86)");
   }
}


/*------------------------------------------------------------*/
/*--- JMP helpers                                          ---*/
/*------------------------------------------------------------*/

static void jmp_lit( /*MOD*/DisResult* dres,
                     IRJumpKind kind, Addr32 d32 )
{
   vassert(dres->whatNext    == Dis_Continue);
   vassert(dres->len         == 0);
   vassert(dres->continueAt  == 0);
   vassert(dres->jk_StopHere == Ijk_INVALID);
   dres->whatNext    = Dis_StopHere;
   dres->jk_StopHere = kind;
   stmt( IRStmt_Put( OFFB_EIP, mkU32(d32) ) );
}

static void jmp_treg( /*MOD*/DisResult* dres,
                      IRJumpKind kind, IRTemp t )
{
   vassert(dres->whatNext    == Dis_Continue);
   vassert(dres->len         == 0);
   vassert(dres->continueAt  == 0);
   vassert(dres->jk_StopHere == Ijk_INVALID);
   dres->whatNext    = Dis_StopHere;
   dres->jk_StopHere = kind;
   stmt( IRStmt_Put( OFFB_EIP, mkexpr(t) ) );
}

static 
void jcc_01( /*MOD*/DisResult* dres,
             X86Condcode cond, Addr32 d32_false, Addr32 d32_true )
{
   Bool        invert;
   X86Condcode condPos;
   vassert(dres->whatNext    == Dis_Continue);
   vassert(dres->len         == 0);
   vassert(dres->continueAt  == 0);
   vassert(dres->jk_StopHere == Ijk_INVALID);
   dres->whatNext    = Dis_StopHere;
   dres->jk_StopHere = Ijk_Boring;
   condPos = positiveIse_X86Condcode ( cond, &invert );
   if (invert) {
      stmt( IRStmt_Exit( mk_x86g_calculate_condition(condPos),
                         Ijk_Boring,
                         IRConst_U32(d32_false),
                         OFFB_EIP ) );
      stmt( IRStmt_Put( OFFB_EIP, mkU32(d32_true) ) );
   } else {
      stmt( IRStmt_Exit( mk_x86g_calculate_condition(condPos),
                         Ijk_Boring,
                         IRConst_U32(d32_true),
                         OFFB_EIP ) );
      stmt( IRStmt_Put( OFFB_EIP, mkU32(d32_false) ) );
   }
}

/*------------------------------------------------------------*/
/*--- Disassembling addressing modes                       ---*/
/*------------------------------------------------------------*/



static 
const HChar* sorbTxt ( UChar sorb )
{
   switch (sorb) {

      case (UNDEFINED_SEG):    return ""; /* no override */
      case R_CS: return "";
      case R_DS: return "";
      case R_ES: return "";
      case R_SS: return "";
      case R_CS | EXPLICIT_BIT: return "%cs:";
      case R_DS | EXPLICIT_BIT: return "%ds:";
      case R_ES | EXPLICIT_BIT: return "%es:";
      case R_SS | EXPLICIT_BIT: return "%ss:";
      default: vpanic("sorbTxt(x86,guest)");
   }
}


static IRTemp disAMode_copy2tmp ( IRExpr* addr32 )
{
   IRTemp tmp = newTemp(Ity_I32);
   assign( tmp, addr32 );
   return tmp;
}

static
IRTemp disAMode ( Int* len, UChar* sorb, Int delta, HChar* buf ) {
   UChar mod_reg_rm = getIByte(delta);
   UChar mod, rm;

   delta++;

   buf[0] = (UChar)0;

   /* squeeze out the reg field from mod_reg_rm, since a 256-entry
      jump table seems a bit excessive.
   */
   mod_reg_rm &= 0xC7;                      /* is now XX000YYY */
   mod_reg_rm  = toUChar(mod_reg_rm | (mod_reg_rm >> 3));
                                            /* is now XX0XXYYY */
   mod_reg_rm &= 0x1F;             /* is now 000XXYYY */
   rm = mod_reg_rm & 0x7;
   mod = mod_reg_rm >> 3;
   Int d;
   /* 0x6 is a special case because we can't
    * deref %bp without displacement */
   if(mod_reg_rm == 0x6)
   {
	 UInt d = getUDisp16(delta);
	 *len = 3;
    if((!ignore_seg_mode) && (*sorb == UNDEFINED_SEG)){
        *sorb = R_DS;
    }
	  DIS(buf, "%s(0x%x)", sorbTxt(*sorb), d);
      return disAMode_copy2tmp(mkU32(d));
   }
   switch(mod){
      case 0x00:
	  d = 0;
	  *len = 1;
	  break;
	  case 0x01:
	  d = getSDisp8(delta);
	  *len = 2;
	  break;
	  case 0x02:
	  d = getSDisp16(delta); //TODO is it really signed?
	  *len = 3;
	  break;
	  case 0x03:
	  vpanic("disAMode(x86): not an addr!");
   }
   switch (rm){
      case 0x00: case 0x01: case 0x04: case 0x05: case 0x07:
      if((!ignore_seg_mode) && (*sorb == UNDEFINED_SEG)){
        *sorb = R_DS;
     }
     break;
      case 0x02: case 0x03: case 0x06:
      if((!ignore_seg_mode) && (*sorb == UNDEFINED_SEG)){
        *sorb = R_SS;
     }
   }
   IRExpr* deref_vaddr;
   switch (rm){
	  case 0x00:
	  deref_vaddr = binop(Iop_Add16,getIReg(2, R_EBX),getIReg(2, R_ESI));
     DIS(buf, "%s%d(%%bx, %%si)",sorbTxt(*sorb) ,d);
	  break;
	  case 0x01:
	  deref_vaddr = binop(Iop_Add16,getIReg(2, R_EBX),getIReg(2, R_EDI));
     DIS(buf, "%s%d(%%bx, %%di)",sorbTxt(*sorb) ,d);
	  break;
	  case 0x02:
	  deref_vaddr = binop(Iop_Add16,getIReg(2, R_EBP),getIReg(2, R_ESI));
     DIS(buf, "%s%d(%%bp, %%si)",sorbTxt(*sorb) ,d);
	  break;
	  case 0x03:
	  deref_vaddr = binop(Iop_Add16,getIReg(2, R_EBP),getIReg(2, R_EDI));
     DIS(buf, "%s%d(%%bp, %%di)",sorbTxt(*sorb) ,d);
	  break;
	  case 0x04:
	  deref_vaddr = IRExpr_Get(OFFB_ESI,szToITy(2));
     DIS(buf, "%s%d(%%si)",sorbTxt(*sorb) ,d);
	  break;
	  case 0x05:
	  deref_vaddr = IRExpr_Get(OFFB_EDI,szToITy(2));
     DIS(buf, "%s%d(%%di)",sorbTxt(*sorb) ,d);
	  break;
	  case 0x06:
	  deref_vaddr = IRExpr_Get(OFFB_EBP,szToITy(2));
     DIS(buf, "%s%d(%%bp)",sorbTxt(*sorb) ,d);
	  break;
	  case 0x07:
	  deref_vaddr = IRExpr_Get(OFFB_EBX,szToITy(2));
     DIS(buf, "%s%d(%%bx)",sorbTxt(*sorb) ,d);
	  break;
   }
   return disAMode_copy2tmp(binop(Iop_Add32,unop(Iop_16Uto32,deref_vaddr),mkU32(d)));

}

/* Code shared by all the string ops */
static
void dis_string_op_increment(Int sz, Int t_inc)
{
   if (sz == 4 || sz == 2) {
      assign( t_inc, 
              binop(Iop_Shl32, IRExpr_Get( OFFB_DFLAG, Ity_I32 ),
                               mkU8(sz/2) ) );
   } else {
      assign( t_inc, 
              IRExpr_Get( OFFB_DFLAG, Ity_I32 ) );
   }
}

static
void dis_string_op( void (*dis_OP)( Int, IRTemp ), 
                    Int sz, const HChar* name, UChar sorb )
{
   IRTemp t_inc = newTemp(Ity_I32);
   vassert(sorb == UNDEFINED_SEG); /* hmm.  so what was the point of passing it in? */
   dis_string_op_increment(sz, t_inc);
   dis_OP( sz, t_inc );
   DIP("%s%c\n", name, nameISize(sz));
}

static 
void dis_MOVS ( Int sz, IRTemp t_inc )
{
   IRType ty = szToITy(sz);
   IRTemp td = newTemp(Ity_I32);   /* EDI */
   IRTemp ts = newTemp(Ity_I32);   /* ESI */

   assign( td, getIReg(4, R_EDI) );
   assign( ts, getIReg(4, R_ESI) );

   storeRealLE( mkexpr(td),R_ES, loadRealLE(ty, R_DS,mkexpr(ts)) );

   putIReg( 4, R_EDI, binop(Iop_Add32, mkexpr(td), mkexpr(t_inc)) );
   putIReg( 4, R_ESI, binop(Iop_Add32, mkexpr(ts), mkexpr(t_inc)) );
}

static 
void dis_LODS ( Int sz, IRTemp t_inc )
{
   IRType ty = szToITy(sz);
   IRTemp ts = newTemp(Ity_I32);   /* ESI */

   assign( ts, getIReg(4, R_ESI) );

   putIReg( sz, R_EAX, loadRealLE(ty,R_DS, mkexpr(ts)) );

   putIReg( 4, R_ESI, binop(Iop_Add32, mkexpr(ts), mkexpr(t_inc)) );
}

static 
void dis_STOS ( Int sz, IRTemp t_inc )
{
   IRType ty = szToITy(sz);
   IRTemp ta = newTemp(ty);        /* EAX */
   IRTemp td = newTemp(Ity_I32);   /* EDI */

   assign( ta, getIReg(sz, R_EAX) );
   assign( td, getIReg(4, R_EDI) );

   storeRealLE( mkexpr(td), R_ES, mkexpr(ta) );

   putIReg( 4, R_EDI, binop(Iop_Add32, mkexpr(td), mkexpr(t_inc)) );
}

static 
void dis_CMPS ( Int sz, IRTemp t_inc )
{
   IRType ty  = szToITy(sz);
   IRTemp tdv = newTemp(ty);      /* (EDI) */
   IRTemp tsv = newTemp(ty);      /* (ESI) */
   IRTemp td  = newTemp(Ity_I32); /*  EDI  */
   IRTemp ts  = newTemp(Ity_I32); /*  ESI  */

   assign( td, getIReg(4, R_EDI) );
   assign( ts, getIReg(4, R_ESI) );

   assign( tdv, loadRealLE(ty,R_ES,mkexpr(td)) );
   assign( tsv, loadRealLE(ty,R_DS,mkexpr(ts)) );

   setFlags_DEP1_DEP2 ( Iop_Sub8, tsv, tdv, ty );

   putIReg(4, R_EDI, binop(Iop_Add32, mkexpr(td), mkexpr(t_inc)) );
   putIReg(4, R_ESI, binop(Iop_Add32, mkexpr(ts), mkexpr(t_inc)) );
}

static 
void dis_SCAS ( Int sz, IRTemp t_inc )
{
   IRType ty  = szToITy(sz);
   IRTemp ta  = newTemp(ty);       /*  EAX  */
   IRTemp td  = newTemp(Ity_I32);  /*  EDI  */
   IRTemp tdv = newTemp(ty);       /* (EDI) */

   assign( ta, getIReg(sz, R_EAX) );
   assign( td, getIReg(4, R_EDI) );

   assign( tdv, loadRealLE(ty,R_ES,mkexpr(td)) );
   setFlags_DEP1_DEP2 ( Iop_Sub8, ta, tdv, ty );

   putIReg(4, R_EDI, binop(Iop_Add32, mkexpr(td), mkexpr(t_inc)) );
}


/* Wrap the appropriate string op inside a REP/REPE/REPNE.
   We assume the insn is the last one in the basic block, and so emit a jump
   to the next insn, rather than just falling through. */
static 
void dis_REP_op ( /*MOD*/DisResult* dres,
                  X86Condcode cond,
                  void (*dis_OP)(Int, IRTemp),
                  Int sz, Addr32 eip, Addr32 eip_next, const HChar* name )
{
   IRTemp t_inc = newTemp(Ity_I32);
   IRTemp tc    = newTemp(Ity_I32);  /*  ECX  */

   assign( tc, getIReg(4,R_ECX) );

   stmt( IRStmt_Exit( binop(Iop_CmpEQ32,mkexpr(tc),mkU32(0)),
                      Ijk_Boring,
                      IRConst_U32(eip_next), OFFB_EIP ) );

   putIReg(4, R_ECX, binop(Iop_Sub32, mkexpr(tc), mkU32(1)) );

   dis_string_op_increment(sz, t_inc);
   dis_OP (sz, t_inc);

   if (cond == X86CondAlways) {
      jmp_lit(dres, Ijk_Boring, eip);
      vassert(dres->whatNext == Dis_StopHere);
   } else {
      stmt( IRStmt_Exit( mk_x86g_calculate_condition(cond),
                         Ijk_Boring,
                         IRConst_U32(eip), OFFB_EIP ) );
      jmp_lit(dres, Ijk_Boring, eip_next);
      vassert(dres->whatNext == Dis_StopHere);
   }
   DIP("%s%c\n", name, nameISize(sz));
}



static UInt lengthAMode ( Int delta )
{
    UChar mod_reg_rm = getIByte(delta); delta++;

   /* squeeze out the reg field from mod_reg_rm, since a 256-entry
      jump table seems a bit excessive. 
   */
   mod_reg_rm &= 0xC7;               /* is now XX000YYY */
   mod_reg_rm  = toUChar(mod_reg_rm | (mod_reg_rm >> 3));  
                                     /* is now XX0XXYYY */
   mod_reg_rm &= 0x1F;               /* is now 000XXYYY */
   switch (mod_reg_rm) {

      case 0x00: case 0x01: case 0x02: case 0x03:
      case 0x04: case 0x05: /* ! 06 */ case 0x07:
      return 1;
      case 0x08: case 0x09: case 0x0a: case 0x0b:
      case 0x0c: case 0x0d: case 0x0e: case 0x0f:
      return 2;
      case 0x10: case 0x11: case 0x12: case 0x13:
      case 0x14: case 0x15: case 0x16: case 0x17:
      case 0x06:
      return 3;
      case 0x18: case 0x19: case 0x1a: case 0x1b:
      case 0x1c: case 0x1d: case 0x1e: case 0x1f:
      return 1;
      default:
         vpanic("lengthAMode16");
         return 0; /*notreached*/
   }
}


/*------------------------------------------------------------*/
/*--- Arithmetic, etc.                                     ---*/
/*------------------------------------------------------------*/

/* IMUL E, G.  Supplied eip points to the modR/M byte. */
static
UInt dis_mul_E_G ( UChar       sorb,
                   Int         size, 
                   Int         delta0 )
{
   Int    alen;
   HChar  dis_buf[50];
   UChar  rm = getIByte(delta0);
   IRType ty = szToITy(size);
   IRTemp te = newTemp(ty);
   IRTemp tg = newTemp(ty);
   IRTemp resLo = newTemp(ty);

   assign( tg, getIReg(size, gregOfRM(rm)) );
   if (epartIsReg(rm)) {
      assign( te, getIReg(size, eregOfRM(rm)) );
   } else {
      IRTemp addr = disAMode( &alen, &sorb, delta0, dis_buf );
      assign( te, loadRealLE(ty,sorb,mkexpr(addr)) );
   }

   setFlags_MUL ( ty, te, tg, X86G_CC_OP_SMULB );

   assign( resLo, binop( mkSizedOp(ty, Iop_Mul8), mkexpr(te), mkexpr(tg) ) );

   putIReg(size, gregOfRM(rm), mkexpr(resLo) );

   if (epartIsReg(rm)) {
      DIP("imul%c %s, %s\n", nameISize(size), 
                             nameIReg(size,eregOfRM(rm)),
                             nameIReg(size,gregOfRM(rm)));
      return 1+delta0;
   } else {
      DIP("imul%c %s, %s\n", nameISize(size), 
                             dis_buf, nameIReg(size,gregOfRM(rm)));
      return alen+delta0;
   }
}


/* Handle binary integer instructions of the form
      op G, E  meaning
      op reg, reg-or-mem
   Is passed the a ptr to the modRM byte, the actual operation, and the
   data size.  Returns the address advanced completely over this
   instruction.

   G(src) is reg.
   E(dst) is reg-or-mem

   If E is reg, -->    GET %E,  tmp
                       OP %G,   tmp
                       PUT tmp, %E
 
   If E is mem, -->    (getAddr E) -> tmpa
                       LD (tmpa), tmpv
                       OP %G, tmpv
                       ST tmpv, (tmpa)
*/
static
UInt dis_op2_G_E ( UChar       sorb,
                   Bool        locked,
                   Bool        addSubCarry,
                   IROp        op8, 
                   Bool        keep,
                   Int         size, 
                   Int         delta0,
                   const HChar* t_x86opc )
{
   HChar   dis_buf[50];
   Int     len;
   IRType  ty   = szToITy(size);
   IRTemp  dst1 = newTemp(ty);
   IRTemp  src  = newTemp(ty);
   IRTemp  dst0 = newTemp(ty);
   UChar   rm   = getIByte(delta0);
   IRTemp  addr = IRTemp_INVALID;

   /* addSubCarry == True indicates the intended operation is
      add-with-carry or subtract-with-borrow. */
   if (addSubCarry) {
      vassert(op8 == Iop_Add8 || op8 == Iop_Sub8);
      vassert(keep);
   }

   if (epartIsReg(rm)) {
      /* Specially handle XOR reg,reg, because that doesn't really
         depend on reg, and doing the obvious thing potentially
         generates a spurious value check failure due to the bogus
         dependency.  Ditto SBB reg,reg.*/
      if ((op8 == Iop_Xor8 || (op8 == Iop_Sub8 && addSubCarry))
          && gregOfRM(rm) == eregOfRM(rm)) {
         putIReg(size, eregOfRM(rm), mkU(ty,0));
      }
      assign(dst0, getIReg(size,eregOfRM(rm)));
      assign(src,  getIReg(size,gregOfRM(rm)));

      if (addSubCarry && op8 == Iop_Add8) {
         helper_ADC( size, dst1, dst0, src,
                     /*no store*/IRTemp_INVALID, IRTemp_INVALID, 0 , -1);
         putIReg(size, eregOfRM(rm), mkexpr(dst1));
      } else
      if (addSubCarry && op8 == Iop_Sub8) {
         helper_SBB( size, dst1, dst0, src,
                     /*no store*/IRTemp_INVALID, IRTemp_INVALID, 0 , -1 );
         putIReg(size, eregOfRM(rm), mkexpr(dst1));
      } else {
         assign(dst1, binop(mkSizedOp(ty,op8), mkexpr(dst0), mkexpr(src)));
         if (isAddSub(op8))
            setFlags_DEP1_DEP2(op8, dst0, src, ty);
         else
            setFlags_DEP1(op8, dst1, ty);
         if (keep)
            putIReg(size, eregOfRM(rm), mkexpr(dst1));
      }

      DIP("%s%c %s,%s\n", t_x86opc, nameISize(size), 
                          nameIReg(size,gregOfRM(rm)),
                          nameIReg(size,eregOfRM(rm)));
      return 1+delta0;
   }

   /* E refers to memory */    
   {
      addr = disAMode ( &len, &sorb, delta0, dis_buf);
      assign(dst0, loadRealLE(ty,sorb,mkexpr(addr)));
      assign(src,  getIReg(size,gregOfRM(rm)));

      if (addSubCarry && op8 == Iop_Add8) {
         if (locked) {
            /* cas-style store */
            helper_ADC( size, dst1, dst0, src,
                        /*store*/addr, dst0/*expVal*/, guest_EIP_curr_instr, sorb );
         } else {
            /* normal store */
            helper_ADC( size, dst1, dst0, src,
                        /*store*/addr, IRTemp_INVALID, 0 , sorb);
         }
      } else
      if (addSubCarry && op8 == Iop_Sub8) {
         if (locked) {
            /* cas-style store */
            helper_SBB( size, dst1, dst0, src,
                        /*store*/addr, dst0/*expVal*/, guest_EIP_curr_instr, sorb );
         } else {
            /* normal store */
            helper_SBB( size, dst1, dst0, src,
                        /*store*/addr, IRTemp_INVALID, 0, sorb );
         }
      } else {
         assign(dst1, binop(mkSizedOp(ty,op8), mkexpr(dst0), mkexpr(src)));
         if (keep) {
            if (locked) {
               if (0) vex_printf("locked case\n" );
               casLE( mkexpr(addr),
                      mkexpr(dst0)/*expval*/, 
                      mkexpr(dst1)/*newval*/, guest_EIP_curr_instr );
            } else {
               if (0) vex_printf("nonlocked case\n");
               storeRealLE(mkexpr(addr), sorb,  mkexpr(dst1));
            }
         }
         if (isAddSub(op8))
            setFlags_DEP1_DEP2(op8, dst0, src, ty);
         else
            setFlags_DEP1(op8, dst1, ty);
      }

      DIP("%s%c %s,%s\n", t_x86opc, nameISize(size), 
                          nameIReg(size,gregOfRM(rm)), dis_buf);
      return len+delta0;
   }
}


/* Handle binary integer instructions of the form
      op E, G  meaning
      op reg-or-mem, reg
   Is passed the a ptr to the modRM byte, the actual operation, and the
   data size.  Returns the address advanced completely over this
   instruction.

   E(src) is reg-or-mem
   G(dst) is reg.

   If E is reg, -->    GET %G,  tmp
                       OP %E,   tmp
                       PUT tmp, %G
 
   If E is mem and OP is not reversible, 
                -->    (getAddr E) -> tmpa
                       LD (tmpa), tmpa
                       GET %G, tmp2
                       OP tmpa, tmp2
                       PUT tmp2, %G

   If E is mem and OP is reversible
                -->    (getAddr E) -> tmpa
                       LD (tmpa), tmpa
                       OP %G, tmpa
                       PUT tmpa, %G
*/
static
UInt dis_op2_E_G ( UChar       sorb,
                   Bool        addSubCarry,
                   IROp        op8, 
                   Bool        keep,
                   Int         size, 
                   Int         delta0,
                   const HChar* t_x86opc )
{
   HChar   dis_buf[50];
   Int     len;
   IRType  ty   = szToITy(size);
   IRTemp  dst1 = newTemp(ty);
   IRTemp  src  = newTemp(ty);
   IRTemp  dst0 = newTemp(ty);
   UChar   rm   = getUChar(delta0);
   IRTemp  addr = IRTemp_INVALID;

   /* addSubCarry == True indicates the intended operation is
      add-with-carry or subtract-with-borrow. */
   if (addSubCarry) {
      vassert(op8 == Iop_Add8 || op8 == Iop_Sub8);
      vassert(keep);
   }

   if (epartIsReg(rm)) {
      /* Specially handle XOR reg,reg, because that doesn't really
         depend on reg, and doing the obvious thing potentially
         generates a spurious value check failure due to the bogus
         dependency.  Ditto SBB reg,reg. */
      if ((op8 == Iop_Xor8 || (op8 == Iop_Sub8 && addSubCarry))
          && gregOfRM(rm) == eregOfRM(rm)) {
         putIReg(size, gregOfRM(rm), mkU(ty,0));
      }
      assign( dst0, getIReg(size,gregOfRM(rm)) );
      assign( src,  getIReg(size,eregOfRM(rm)) );

      if (addSubCarry && op8 == Iop_Add8) {
         helper_ADC( size, dst1, dst0, src,
                     /*no store*/IRTemp_INVALID, IRTemp_INVALID, 0 , -1 );
         putIReg(size, gregOfRM(rm), mkexpr(dst1));
      } else
      if (addSubCarry && op8 == Iop_Sub8) {
         helper_SBB( size, dst1, dst0, src,
                     /*no store*/IRTemp_INVALID, IRTemp_INVALID, 0 , -1 );
         putIReg(size, gregOfRM(rm), mkexpr(dst1));
      } else {
         assign( dst1, binop(mkSizedOp(ty,op8), mkexpr(dst0), mkexpr(src)) );
         if (isAddSub(op8))
            setFlags_DEP1_DEP2(op8, dst0, src, ty);
         else
            setFlags_DEP1(op8, dst1, ty);
         if (keep)
            putIReg(size, gregOfRM(rm), mkexpr(dst1));
      }

      DIP("%s%c %s,%s\n", t_x86opc, nameISize(size), 
                          nameIReg(size,eregOfRM(rm)),
                          nameIReg(size,gregOfRM(rm)));
      return 1+delta0;
   } else {
      /* E refers to memory */
      addr = disAMode ( &len, &sorb, delta0, dis_buf);
      assign( dst0, getIReg(size,gregOfRM(rm)) );
      assign( src,  loadRealLE(szToITy(size),sorb, mkexpr(addr)) );

      if (addSubCarry && op8 == Iop_Add8) {
         helper_ADC( size, dst1, dst0, src,
                     /*no store*/IRTemp_INVALID, IRTemp_INVALID, 0, -1 );
         putIReg(size, gregOfRM(rm), mkexpr(dst1));
      } else
      if (addSubCarry && op8 == Iop_Sub8) {
         helper_SBB( size, dst1, dst0, src,
                     /*no store*/IRTemp_INVALID, IRTemp_INVALID, 0 , -1 );
         putIReg(size, gregOfRM(rm), mkexpr(dst1));
      } else {
         assign( dst1, binop(mkSizedOp(ty,op8), mkexpr(dst0), mkexpr(src)) );
         if (isAddSub(op8))
            setFlags_DEP1_DEP2(op8, dst0, src, ty);
         else
            setFlags_DEP1(op8, dst1, ty);
         if (keep)
            putIReg(size, gregOfRM(rm), mkexpr(dst1));
      }

      DIP("%s%c %s,%s\n", t_x86opc, nameISize(size), 
                          dis_buf,nameIReg(size,gregOfRM(rm)));
      return len+delta0;
   }
}


/* op $immediate, AL/AX/EAX. */
static
UInt dis_op_imm_A ( Int    size,
                    Bool   carrying,
                    IROp   op8,
                    Bool   keep,
                    Int    delta,
                    const HChar* t_x86opc )
{
   IRType ty   = szToITy(size);
   IRTemp dst0 = newTemp(ty);
   IRTemp src  = newTemp(ty);
   IRTemp dst1 = newTemp(ty);
   UInt lit    = getUDisp(size,delta);
   assign(dst0, getIReg(size,R_EAX));
   assign(src,  mkU(ty,lit));

   if (isAddSub(op8) && !carrying) {
      assign(dst1, binop(mkSizedOp(ty,op8), mkexpr(dst0), mkexpr(src)) );
      setFlags_DEP1_DEP2(op8, dst0, src, ty);
   } 
   else
   if (isLogic(op8)) {
      vassert(!carrying);
      assign(dst1, binop(mkSizedOp(ty,op8), mkexpr(dst0), mkexpr(src)) );
      setFlags_DEP1(op8, dst1, ty);
   } 
   else
   if (op8 == Iop_Add8 && carrying) {
      helper_ADC( size, dst1, dst0, src,
                  /*no store*/IRTemp_INVALID, IRTemp_INVALID, 0, -1 );
   }
   else
   if (op8 == Iop_Sub8 && carrying) {
      helper_SBB( size, dst1, dst0, src,
                  /*no store*/IRTemp_INVALID, IRTemp_INVALID, 0, -1  );
   }
   else
      vpanic("dis_op_imm_A(x86,guest)");

   if (keep)
      putIReg(size, R_EAX, mkexpr(dst1));

   DIP("%s%c $0x%x, %s\n", t_x86opc, nameISize(size), 
                           lit, nameIReg(size,R_EAX));
   return delta+size;
}

/* Sign- and Zero-extending moves. */
static
UInt dis_movx_E_G ( UChar      sorb,
                    Int delta, Int szs, Int szd, Bool sign_extend )
{
   UChar rm = getIByte(delta);
   if (epartIsReg(rm)) {
      if (szd == szs) {
         // mutant case.  See #250799
         putIReg(szd, gregOfRM(rm),
                           getIReg(szs,eregOfRM(rm)));
      } else {
         // normal case
         putIReg(szd, gregOfRM(rm),
                      unop(mkWidenOp(szs,szd,sign_extend), 
                           getIReg(szs,eregOfRM(rm))));
      }
      DIP("mov%c%c%c %s,%s\n", sign_extend ? 's' : 'z',
                               nameISize(szs), nameISize(szd),
                               nameIReg(szs,eregOfRM(rm)),
                               nameIReg(szd,gregOfRM(rm)));
      return 1+delta;
   }

   /* E refers to memory */    
   {
      Int    len;
      HChar  dis_buf[50];
      IRTemp addr = disAMode ( &len, &sorb, delta, dis_buf );
      if (szd == szs) {
         // mutant case.  See #250799
         putIReg(szd, gregOfRM(rm),
                           loadRealLE(szToITy(szs),sorb,mkexpr(addr)));
      } else {
         // normal case
         putIReg(szd, gregOfRM(rm),
                      unop(mkWidenOp(szs,szd,sign_extend), 
                           loadRealLE(szToITy(szs),sorb,mkexpr(addr))));
      }
      DIP("mov%c%c%c %s,%s\n", sign_extend ? 's' : 'z',
                               nameISize(szs), nameISize(szd),
                               dis_buf, nameIReg(szd,gregOfRM(rm)));
      return len+delta;
   }
}


/* Generate code to divide ArchRegs EDX:EAX / DX:AX / AX by the 32 /
   16 / 8 bit quantity in the given IRTemp.  */
static
void codegen_div ( Int sz, IRTemp t, Bool signed_divide )
{
   IROp   op    = signed_divide ? Iop_DivModS64to32 : Iop_DivModU64to32;
   IRTemp src64 = newTemp(Ity_I64);
   IRTemp dst64 = newTemp(Ity_I64);
   switch (sz) {
      case 4:
         assign( src64, binop(Iop_32HLto64, 
                              getIReg(4,R_EDX), getIReg(4,R_EAX)) );
         assign( dst64, binop(op, mkexpr(src64), mkexpr(t)) );
         putIReg( 4, R_EAX, unop(Iop_64to32,mkexpr(dst64)) );
         putIReg( 4, R_EDX, unop(Iop_64HIto32,mkexpr(dst64)) );
         break;
      case 2: {
         IROp widen3264 = signed_divide ? Iop_32Sto64 : Iop_32Uto64;
         IROp widen1632 = signed_divide ? Iop_16Sto32 : Iop_16Uto32;
         assign( src64, unop(widen3264,
                             binop(Iop_16HLto32, 
                                   getIReg(2,R_EDX), getIReg(2,R_EAX))) );
         assign( dst64, binop(op, mkexpr(src64), unop(widen1632,mkexpr(t))) );
         putIReg( 2, R_EAX, unop(Iop_32to16,unop(Iop_64to32,mkexpr(dst64))) );
         putIReg( 2, R_EDX, unop(Iop_32to16,unop(Iop_64HIto32,mkexpr(dst64))) );
         break;
      }
      case 1: {
         IROp widen3264 = signed_divide ? Iop_32Sto64 : Iop_32Uto64;
         IROp widen1632 = signed_divide ? Iop_16Sto32 : Iop_16Uto32;
         IROp widen816  = signed_divide ? Iop_8Sto16  : Iop_8Uto16;
         assign( src64, unop(widen3264, unop(widen1632, getIReg(2,R_EAX))) );
         assign( dst64, 
                 binop(op, mkexpr(src64), 
                           unop(widen1632, unop(widen816, mkexpr(t)))) );
         putIReg( 1, R_AL, unop(Iop_16to8, unop(Iop_32to16,
                           unop(Iop_64to32,mkexpr(dst64)))) );
         putIReg( 1, R_AH, unop(Iop_16to8, unop(Iop_32to16,
                           unop(Iop_64HIto32,mkexpr(dst64)))) );
         break;
      }
      default: vpanic("codegen_div(x86)");
   }
}


static 
UInt dis_Grp1 ( UChar sorb, Bool locked,
                Int delta, UChar modrm, 
                Int am_sz, Int d_sz, Int sz, UInt d32 )
{
   Int     len;
   HChar   dis_buf[50];
   IRType  ty   = szToITy(sz);
   IRTemp  dst1 = newTemp(ty);
   IRTemp  src  = newTemp(ty);
   IRTemp  dst0 = newTemp(ty);
   IRTemp  addr = IRTemp_INVALID;
   IROp    op8  = Iop_INVALID;
   UInt    mask = sz==1 ? 0xFF : (sz==2 ? 0xFFFF : 0xFFFFFFFF);

   switch (gregOfRM(modrm)) {
      case 0: op8 = Iop_Add8; break;  case 1: op8 = Iop_Or8;  break;
      case 2: break;  // ADC
      case 3: break;  // SBB
      case 4: op8 = Iop_And8; break;  case 5: op8 = Iop_Sub8; break;
      case 6: op8 = Iop_Xor8; break;  case 7: op8 = Iop_Sub8; break;
      /*NOTREACHED*/
      default: vpanic("dis_Grp1: unhandled case");
   }

   if (epartIsReg(modrm)) {
      vassert(am_sz == 1);

      assign(dst0, getIReg(sz,eregOfRM(modrm)));
      assign(src,  mkU(ty,d32 & mask));

      if (gregOfRM(modrm) == 2 /* ADC */) {
         helper_ADC( sz, dst1, dst0, src,
                     /*no store*/IRTemp_INVALID, IRTemp_INVALID, 0,-1 );
      } else 
      if (gregOfRM(modrm) == 3 /* SBB */) {
         helper_SBB( sz, dst1, dst0, src,
                     /*no store*/IRTemp_INVALID, IRTemp_INVALID, 0,-1 );
      } else {
         assign(dst1, binop(mkSizedOp(ty,op8), mkexpr(dst0), mkexpr(src)));
         if (isAddSub(op8))
            setFlags_DEP1_DEP2(op8, dst0, src, ty);
         else
            setFlags_DEP1(op8, dst1, ty);
      }

      if (gregOfRM(modrm) < 7)
         putIReg(sz, eregOfRM(modrm), mkexpr(dst1));

      delta += (am_sz + d_sz);
      DIP("%s%c $0x%x, %s\n", nameGrp1(gregOfRM(modrm)), nameISize(sz), d32, 
                              nameIReg(sz,eregOfRM(modrm)));
   } else {
      addr = disAMode ( &len, &sorb, delta, dis_buf);

      assign(dst0, loadRealLE(ty, sorb,mkexpr(addr)));
      assign(src, mkU(ty,d32 & mask));

      if (gregOfRM(modrm) == 2 /* ADC */) {
         if (locked) {
            /* cas-style store */
            helper_ADC( sz, dst1, dst0, src,
                       /*store*/addr, dst0/*expVal*/, guest_EIP_curr_instr, sorb );
         } else {
            /* normal store */
            helper_ADC( sz, dst1, dst0, src,
                        /*store*/addr, IRTemp_INVALID, 0, sorb );
         }
      } else 
      if (gregOfRM(modrm) == 3 /* SBB */) {
         if (locked) {
            /* cas-style store */
            helper_SBB( sz, dst1, dst0, src,
                       /*store*/addr, dst0/*expVal*/, guest_EIP_curr_instr, sorb );
         } else {
            /* normal store */
            helper_SBB( sz, dst1, dst0, src,
                        /*store*/addr, IRTemp_INVALID, 0, sorb );
         }
      } else {
         assign(dst1, binop(mkSizedOp(ty,op8), mkexpr(dst0), mkexpr(src)));
         if (gregOfRM(modrm) < 7) {
            if (locked) {
               casLE( mkexpr(addr), mkexpr(dst0)/*expVal*/, 
                                    mkexpr(dst1)/*newVal*/,
                                    guest_EIP_curr_instr );
            } else {
               storeRealLE(mkexpr(addr),sorb, mkexpr(dst1));
            }
         }
         if (isAddSub(op8))
            setFlags_DEP1_DEP2(op8, dst0, src, ty);
         else
            setFlags_DEP1(op8, dst1, ty);
      }

      delta += (len+d_sz);
      DIP("%s%c $0x%x, %s\n", nameGrp1(gregOfRM(modrm)), nameISize(sz),
                              d32, dis_buf);
   }
   return delta;
}


/* Group 2 extended opcodes.  shift_expr must be an 8-bit typed
   expression. */

static
UInt dis_Grp2 ( UChar sorb,
                Int delta, UChar modrm,
                Int am_sz, Int d_sz, Int sz, IRExpr* shift_expr,
                const HChar* shift_expr_txt, Bool* decode_OK )
{
   /* delta on entry points at the modrm byte. */
   HChar  dis_buf[50];
   Int    len;
   Bool   isShift, isRotate, isRotateC;
   IRType ty    = szToITy(sz);
   IRTemp dst0  = newTemp(ty);
   IRTemp dst1  = newTemp(ty);
   IRTemp addr  = IRTemp_INVALID;

   *decode_OK = True;

   vassert(sz == 1 || sz == 2 || sz == 4);

   /* Put value to shift/rotate in dst0. */
   if (epartIsReg(modrm)) {
      assign(dst0, getIReg(sz, eregOfRM(modrm)));
      delta += (am_sz + d_sz);
   } else {
      addr = disAMode ( &len, &sorb, delta, dis_buf);
      assign(dst0, loadRealLE(ty,sorb,mkexpr(addr)));
      delta += len + d_sz;
   }

   isShift = False;
   switch (gregOfRM(modrm)) { case 4: case 5: case 6: case 7: isShift = True; }

   isRotate = False;
   switch (gregOfRM(modrm)) { case 0: case 1: isRotate = True; }

   isRotateC = False;
   switch (gregOfRM(modrm)) { case 2: case 3: isRotateC = True; }

   if (!isShift && !isRotate && !isRotateC) {
      /*NOTREACHED*/
      vpanic("dis_Grp2(Reg): unhandled case(x86)");
   }

   if (isRotateC) {
      /* call a helper; these insns are so ridiculous they do not
         deserve better */
      Bool     left = toBool(gregOfRM(modrm) == 2);
      IRTemp   r64  = newTemp(Ity_I64);
      IRExpr** args 
         = mkIRExprVec_4( widenUto32(mkexpr(dst0)), /* thing to rotate */
                          widenUto32(shift_expr),   /* rotate amount */
                          widenUto32(mk_x86g_calculate_eflags_all()),
                          mkU32(sz) );
      assign( r64, mkIRExprCCall(
                      Ity_I64, 
                      0/*regparm*/, 
                      left ? "x86g_calculate_RCL" : "x86g_calculate_RCR", 
                      left ? &x86g_calculate_RCL  : &x86g_calculate_RCR,
                      args
                   )
            );
      /* new eflags in hi half r64; new value in lo half r64 */
      assign( dst1, narrowTo(ty, unop(Iop_64to32, mkexpr(r64))) );
      stmt( IRStmt_Put( OFFB_CC_OP,   mkU32(X86G_CC_OP_COPY) ));
      stmt( IRStmt_Put( OFFB_CC_DEP1, unop(Iop_64HIto32, mkexpr(r64)) ));
      stmt( IRStmt_Put( OFFB_CC_DEP2, mkU32(0) ));
      /* Set NDEP even though it isn't used.  This makes redundant-PUT
         elimination of previous stores to this field work better. */
      stmt( IRStmt_Put( OFFB_CC_NDEP, mkU32(0) ));
   }

   if (isShift) {

      IRTemp pre32     = newTemp(Ity_I32);
      IRTemp res32     = newTemp(Ity_I32);
      IRTemp res32ss   = newTemp(Ity_I32);
      IRTemp shift_amt = newTemp(Ity_I8);
      IROp   op32;

      switch (gregOfRM(modrm)) { 
         case 4: op32 = Iop_Shl32; break;
         case 5: op32 = Iop_Shr32; break;
         case 6: op32 = Iop_Shl32; break;
         case 7: op32 = Iop_Sar32; break;
         /*NOTREACHED*/
         default: vpanic("dis_Grp2:shift"); break;
      }

      /* Widen the value to be shifted to 32 bits, do the shift, and
         narrow back down.  This seems surprisingly long-winded, but
         unfortunately the Intel semantics requires that 8/16-bit
         shifts give defined results for shift values all the way up
         to 31, and this seems the simplest way to do it.  It has the
         advantage that the only IR level shifts generated are of 32
         bit values, and the shift amount is guaranteed to be in the
         range 0 .. 31, thereby observing the IR semantics requiring
         all shift values to be in the range 0 .. 2^word_size-1. */

      /* shift_amt = shift_expr & 31, regardless of operation size */
      assign( shift_amt, binop(Iop_And8, shift_expr, mkU8(31)) );

      /* suitably widen the value to be shifted to 32 bits. */
      assign( pre32, op32==Iop_Sar32 ? widenSto32(mkexpr(dst0))
                                     : widenUto32(mkexpr(dst0)) );

      /* res32 = pre32 `shift` shift_amt */
      assign( res32, binop(op32, mkexpr(pre32), mkexpr(shift_amt)) );

      /* res32ss = pre32 `shift` ((shift_amt - 1) & 31) */
      assign( res32ss,
              binop(op32,
                    mkexpr(pre32), 
                    binop(Iop_And8,
                          binop(Iop_Sub8,
                                mkexpr(shift_amt), mkU8(1)),
                          mkU8(31))) );

      /* Build the flags thunk. */
      setFlags_DEP1_DEP2_shift(op32, res32, res32ss, ty, shift_amt);

      /* Narrow the result back down. */
      assign( dst1, narrowTo(ty, mkexpr(res32)) );

   } /* if (isShift) */

   else 
   if (isRotate) {
      Int    ccOp      = ty==Ity_I8 ? 0 : (ty==Ity_I16 ? 1 : 2);
      Bool   left      = toBool(gregOfRM(modrm) == 0);
      IRTemp rot_amt   = newTemp(Ity_I8);
      IRTemp rot_amt32 = newTemp(Ity_I8);
      IRTemp oldFlags  = newTemp(Ity_I32);

      /* rot_amt = shift_expr & mask */
      /* By masking the rotate amount thusly, the IR-level Shl/Shr
         expressions never shift beyond the word size and thus remain
         well defined. */
      assign(rot_amt32, binop(Iop_And8, shift_expr, mkU8(31)));

      if (ty == Ity_I32)
         assign(rot_amt, mkexpr(rot_amt32));
      else
         assign(rot_amt, binop(Iop_And8, mkexpr(rot_amt32), mkU8(8*sz-1)));

      if (left) {

         /* dst1 = (dst0 << rot_amt) | (dst0 >>u (wordsize-rot_amt)) */
         assign(dst1, 
            binop( mkSizedOp(ty,Iop_Or8),
                   binop( mkSizedOp(ty,Iop_Shl8), 
                          mkexpr(dst0),
                          mkexpr(rot_amt)
                   ),
                   binop( mkSizedOp(ty,Iop_Shr8), 
                          mkexpr(dst0), 
                          binop(Iop_Sub8,mkU8(8*sz), mkexpr(rot_amt))
                   )
            )
         );
         ccOp += X86G_CC_OP_ROLB;

      } else { /* right */

         /* dst1 = (dst0 >>u rot_amt) | (dst0 << (wordsize-rot_amt)) */
         assign(dst1, 
            binop( mkSizedOp(ty,Iop_Or8),
                   binop( mkSizedOp(ty,Iop_Shr8), 
                          mkexpr(dst0),
                          mkexpr(rot_amt)
                   ),
                   binop( mkSizedOp(ty,Iop_Shl8), 
                          mkexpr(dst0), 
                          binop(Iop_Sub8,mkU8(8*sz), mkexpr(rot_amt))
                   )
            )
         );
         ccOp += X86G_CC_OP_RORB;

      }

      /* dst1 now holds the rotated value.  Build flag thunk.  We
         need the resulting value for this, and the previous flags.
         Except don't set it if the rotate count is zero. */

      assign(oldFlags, mk_x86g_calculate_eflags_all());

      /* rot_amt32 :: Ity_I8.  We need to convert it to I1. */
      IRTemp rot_amt32b = newTemp(Ity_I1);
      assign(rot_amt32b, binop(Iop_CmpNE8, mkexpr(rot_amt32), mkU8(0)) );

      /* CC_DEP1 is the rotated value.  CC_NDEP is flags before. */
      stmt( IRStmt_Put( OFFB_CC_OP,
                        IRExpr_ITE( mkexpr(rot_amt32b),
                                    mkU32(ccOp),
                                    IRExpr_Get(OFFB_CC_OP,Ity_I32) ) ));
      stmt( IRStmt_Put( OFFB_CC_DEP1, 
                        IRExpr_ITE( mkexpr(rot_amt32b),
                                    widenUto32(mkexpr(dst1)),
                                    IRExpr_Get(OFFB_CC_DEP1,Ity_I32) ) ));
      stmt( IRStmt_Put( OFFB_CC_DEP2, 
                        IRExpr_ITE( mkexpr(rot_amt32b),
                                    mkU32(0),
                                    IRExpr_Get(OFFB_CC_DEP2,Ity_I32) ) ));
      stmt( IRStmt_Put( OFFB_CC_NDEP, 
                        IRExpr_ITE( mkexpr(rot_amt32b),
                                    mkexpr(oldFlags),
                                    IRExpr_Get(OFFB_CC_NDEP,Ity_I32) ) ));
   } /* if (isRotate) */

   /* Save result, and finish up. */
   if (epartIsReg(modrm)) {
      putIReg(sz, eregOfRM(modrm), mkexpr(dst1));
      if (vex_traceflags & VEX_TRACE_FE) {
         vex_printf("%s%c ",
                    nameGrp2(gregOfRM(modrm)), nameISize(sz) );
         if (shift_expr_txt)
            vex_printf("%s", shift_expr_txt);
         else
            ppIRExpr(shift_expr);
         vex_printf(", %s\n", nameIReg(sz,eregOfRM(modrm)));
      }
   } else {
      storeRealLE(mkexpr(addr),sorb, mkexpr(dst1));
      if (vex_traceflags & VEX_TRACE_FE) {
         vex_printf("%s%c ",
                    nameGrp2(gregOfRM(modrm)), nameISize(sz) );
         if (shift_expr_txt)
            vex_printf("%s", shift_expr_txt);
         else
            ppIRExpr(shift_expr);
         vex_printf(", %s\n", dis_buf);
      }
   }
   return delta;
}


/* Group 8 extended opcodes (but BT/BTS/BTC/BTR only). */
static
UInt dis_Grp8_Imm ( UChar sorb,
                    Bool locked,
                    Int delta, UChar modrm,
                    Int am_sz, Int sz, UInt src_val,
                    Bool* decode_OK )
{
   /* src_val denotes a d8.
      And delta on entry points at the modrm byte. */

   IRType ty     = szToITy(sz);
   IRTemp t2     = newTemp(Ity_I32);
   IRTemp t2m    = newTemp(Ity_I32);
   IRTemp t_addr = IRTemp_INVALID;
   HChar  dis_buf[50];
   UInt   mask;

   /* we're optimists :-) */
   *decode_OK = True;

   /* Limit src_val -- the bit offset -- to something within a word.
      The Intel docs say that literal offsets larger than a word are
      masked in this way. */
   switch (sz) {
      case 2:  src_val &= 15; break;
      case 4:  src_val &= 31; break;
      default: *decode_OK = False; return delta;
   }

   /* Invent a mask suitable for the operation. */
   switch (gregOfRM(modrm)) {
      case 4: /* BT */  mask = 0;               break;
      case 5: /* BTS */ mask = 1 << src_val;    break;
      case 6: /* BTR */ mask = ~(1 << src_val); break;
      case 7: /* BTC */ mask = 1 << src_val;    break;
         /* If this needs to be extended, probably simplest to make a
            new function to handle the other cases (0 .. 3).  The
            Intel docs do however not indicate any use for 0 .. 3, so
            we don't expect this to happen. */
      default: *decode_OK = False; return delta;
   }

   /* Fetch the value to be tested and modified into t2, which is
      32-bits wide regardless of sz. */
   if (epartIsReg(modrm)) {
      vassert(am_sz == 1);
      assign( t2, widenUto32(getIReg(sz, eregOfRM(modrm))) );
      delta += (am_sz + 1);
      DIP("%s%c $0x%x, %s\n", nameGrp8(gregOfRM(modrm)), nameISize(sz),
                              src_val, nameIReg(sz,eregOfRM(modrm)));
   } else {
      Int len;
      t_addr = disAMode ( &len, &sorb, delta, dis_buf);
      delta  += (len+1);
      assign( t2, widenUto32(loadRealLE(ty,sorb, mkexpr(t_addr))) );
      DIP("%s%c $0x%x, %s\n", nameGrp8(gregOfRM(modrm)), nameISize(sz),
                              src_val, dis_buf);
   }

   /* Compute the new value into t2m, if non-BT. */
   switch (gregOfRM(modrm)) {
      case 4: /* BT */
         break;
      case 5: /* BTS */
         assign( t2m, binop(Iop_Or32, mkU32(mask), mkexpr(t2)) );
         break;
      case 6: /* BTR */
         assign( t2m, binop(Iop_And32, mkU32(mask), mkexpr(t2)) );
         break;
      case 7: /* BTC */
         assign( t2m, binop(Iop_Xor32, mkU32(mask), mkexpr(t2)) );
         break;
      default: 
         /*NOTREACHED*/ /*the previous switch guards this*/
         vassert(0);
   }

   /* Write the result back, if non-BT.  If the CAS fails then we
      side-exit from the trace at this point, and so the flag state is
      not affected.  This is of course as required. */
   if (gregOfRM(modrm) != 4 /* BT */) {
      if (epartIsReg(modrm)) {
         putIReg(sz, eregOfRM(modrm), narrowTo(ty, mkexpr(t2m)));
      } else {
         if (locked) {
            casLE( mkexpr(t_addr),
                   narrowTo(ty, mkexpr(t2))/*expd*/,
                   narrowTo(ty, mkexpr(t2m))/*new*/,
                   guest_EIP_curr_instr );
         } else {
            storeRealLE(mkexpr(t_addr),sorb, narrowTo(ty, mkexpr(t2m)));
         }
      }
   }

   /* Copy relevant bit from t2 into the carry flag. */
   /* Flags: C=selected bit, O,S,Z,A,P undefined, so are set to zero. */
   stmt( IRStmt_Put( OFFB_CC_OP,   mkU32(X86G_CC_OP_COPY) ));
   stmt( IRStmt_Put( OFFB_CC_DEP2, mkU32(0) ));
   stmt( IRStmt_Put( 
            OFFB_CC_DEP1,
            binop(Iop_And32,
                  binop(Iop_Shr32, mkexpr(t2), mkU8(src_val)),
                  mkU32(1))
       ));
   /* Set NDEP even though it isn't used.  This makes redundant-PUT
      elimination of previous stores to this field work better. */
   stmt( IRStmt_Put( OFFB_CC_NDEP, mkU32(0) ));

   return delta;
}


/* Signed/unsigned widening multiply.  Generate IR to multiply the
   value in EAX/AX/AL by the given IRTemp, and park the result in
   EDX:EAX/DX:AX/AX.
*/
static void codegen_mulL_A_D ( Int sz, Bool syned, 
                               IRTemp tmp, const HChar* tmp_txt )
{
   IRType ty = szToITy(sz);
   IRTemp t1 = newTemp(ty);

   assign( t1, getIReg(sz, R_EAX) );

   switch (ty) {
      case Ity_I32: {
         IRTemp res64   = newTemp(Ity_I64);
         IRTemp resHi   = newTemp(Ity_I32);
         IRTemp resLo   = newTemp(Ity_I32);
         IROp   mulOp   = syned ? Iop_MullS32 : Iop_MullU32;
         UInt   tBaseOp = syned ? X86G_CC_OP_SMULB : X86G_CC_OP_UMULB;
         setFlags_MUL ( Ity_I32, t1, tmp, tBaseOp );
         assign( res64, binop(mulOp, mkexpr(t1), mkexpr(tmp)) );
         assign( resHi, unop(Iop_64HIto32,mkexpr(res64)));
         assign( resLo, unop(Iop_64to32,mkexpr(res64)));
         putIReg(4, R_EDX, mkexpr(resHi));
         putIReg(4, R_EAX, mkexpr(resLo));
         break;
      }
      case Ity_I16: {
         IRTemp res32   = newTemp(Ity_I32);
         IRTemp resHi   = newTemp(Ity_I16);
         IRTemp resLo   = newTemp(Ity_I16);
         IROp   mulOp   = syned ? Iop_MullS16 : Iop_MullU16;
         UInt   tBaseOp = syned ? X86G_CC_OP_SMULB : X86G_CC_OP_UMULB;
         setFlags_MUL ( Ity_I16, t1, tmp, tBaseOp );
         assign( res32, binop(mulOp, mkexpr(t1), mkexpr(tmp)) );
         assign( resHi, unop(Iop_32HIto16,mkexpr(res32)));
         assign( resLo, unop(Iop_32to16,mkexpr(res32)));
         putIReg(2, R_EDX, mkexpr(resHi));
         putIReg(2, R_EAX, mkexpr(resLo));
         break;
      }
      case Ity_I8: {
         IRTemp res16   = newTemp(Ity_I16);
         IRTemp resHi   = newTemp(Ity_I8);
         IRTemp resLo   = newTemp(Ity_I8);
         IROp   mulOp   = syned ? Iop_MullS8 : Iop_MullU8;
         UInt   tBaseOp = syned ? X86G_CC_OP_SMULB : X86G_CC_OP_UMULB;
         setFlags_MUL ( Ity_I8, t1, tmp, tBaseOp );
         assign( res16, binop(mulOp, mkexpr(t1), mkexpr(tmp)) );
         assign( resHi, unop(Iop_16HIto8,mkexpr(res16)));
         assign( resLo, unop(Iop_16to8,mkexpr(res16)));
         putIReg(2, R_EAX, mkexpr(res16));
         break;
      }
      default:
         vpanic("codegen_mulL_A_D(x86)");
   }
   DIP("%s%c %s\n", syned ? "imul" : "mul", nameISize(sz), tmp_txt);
}


/* Group 3 extended opcodes. */
static 
UInt dis_Grp3 ( UChar sorb, Bool locked, Int sz, Int delta, Bool* decode_OK )
{
   UInt    d32;
   UChar   modrm;
   HChar   dis_buf[50];
   Int     len;
   IRTemp  addr;
   IRType  ty = szToITy(sz);
   IRTemp  t1 = newTemp(ty);
   IRTemp dst1, src, dst0;

   *decode_OK = True; /* may change this later */

   modrm = getIByte(delta);

   if (locked && (gregOfRM(modrm) != 2 && gregOfRM(modrm) != 3)) {
      /* LOCK prefix only allowed with not and neg subopcodes */
      *decode_OK = False;
      return delta;
   }

   if (epartIsReg(modrm)) {
      switch (gregOfRM(modrm)) {
         case 0: { /* TEST */
            delta++; d32 = getUDisp(sz, delta); delta += sz;
            dst1 = newTemp(ty);
            assign(dst1, binop(mkSizedOp(ty,Iop_And8),
                               getIReg(sz,eregOfRM(modrm)),
                               mkU(ty,d32)));
            setFlags_DEP1( Iop_And8, dst1, ty );
            DIP("test%c $0x%x, %s\n", nameISize(sz), d32, 
                                      nameIReg(sz, eregOfRM(modrm)));
            break;
         }
         case 1: /* UNDEFINED */
           /* The Intel docs imply this insn is undefined and binutils
              agrees.  Unfortunately Core 2 will run it (with who
              knows what result?)  sandpile.org reckons it's an alias
              for case 0.  We play safe. */
           *decode_OK = False;
           break;
         case 2: /* NOT */
            delta++;
            putIReg(sz, eregOfRM(modrm),
                        unop(mkSizedOp(ty,Iop_Not8),
                             getIReg(sz, eregOfRM(modrm))));
            DIP("not%c %s\n", nameISize(sz), nameIReg(sz, eregOfRM(modrm)));
            break;
         case 3: /* NEG */
            delta++;
            dst0 = newTemp(ty);
            src  = newTemp(ty);
            dst1 = newTemp(ty);
            assign(dst0, mkU(ty,0));
            assign(src,  getIReg(sz,eregOfRM(modrm)));
            assign(dst1, binop(mkSizedOp(ty,Iop_Sub8), mkexpr(dst0), mkexpr(src)));
            setFlags_DEP1_DEP2(Iop_Sub8, dst0, src, ty);
            putIReg(sz, eregOfRM(modrm), mkexpr(dst1));
            DIP("neg%c %s\n", nameISize(sz), nameIReg(sz, eregOfRM(modrm)));
            break;
         case 4: /* MUL (unsigned widening) */
            delta++;
            src = newTemp(ty);
            assign(src, getIReg(sz,eregOfRM(modrm)));
            codegen_mulL_A_D ( sz, False, src, nameIReg(sz,eregOfRM(modrm)) );
            break;
         case 5: /* IMUL (signed widening) */
            delta++;
            src = newTemp(ty);
            assign(src, getIReg(sz,eregOfRM(modrm)));
            codegen_mulL_A_D ( sz, True, src, nameIReg(sz,eregOfRM(modrm)) );
            break;
         case 6: /* DIV */
            delta++;
            assign( t1, getIReg(sz, eregOfRM(modrm)) );
            codegen_div ( sz, t1, False );
            DIP("div%c %s\n", nameISize(sz), nameIReg(sz, eregOfRM(modrm)));
            break;
         case 7: /* IDIV */
            delta++;
            assign( t1, getIReg(sz, eregOfRM(modrm)) );
            codegen_div ( sz, t1, True );
            DIP("idiv%c %s\n", nameISize(sz), nameIReg(sz, eregOfRM(modrm)));
            break;
         default: 
            /* This can't happen - gregOfRM should return 0 .. 7 only */
            vpanic("Grp3(x86)");
      }
   } else {
      addr = disAMode ( &len, &sorb, delta, dis_buf );
      t1   = newTemp(ty);
      delta += len;
      assign(t1, loadRealLE(ty,sorb, mkexpr(addr)));
      switch (gregOfRM(modrm)) {
         case 0: { /* TEST */
            d32 = getUDisp(sz, delta); delta += sz;
            dst1 = newTemp(ty);
            assign(dst1, binop(mkSizedOp(ty,Iop_And8),
                               mkexpr(t1), mkU(ty,d32)));
            setFlags_DEP1( Iop_And8, dst1, ty );
            DIP("test%c $0x%x, %s\n", nameISize(sz), d32, dis_buf);
            break;
         }
         case 1: /* UNDEFINED */
           /* See comment above on R case */
           *decode_OK = False;
           break;
         case 2: /* NOT */
            dst1 = newTemp(ty);
            assign(dst1, unop(mkSizedOp(ty,Iop_Not8), mkexpr(t1)));
            if (locked) {
               casLE( mkexpr(addr), mkexpr(t1)/*expd*/, mkexpr(dst1)/*new*/,
                                    guest_EIP_curr_instr );
            } else {
               storeRealLE( mkexpr(addr),sorb, mkexpr(dst1) );
            }
            DIP("not%c %s\n", nameISize(sz), dis_buf);
            break;
         case 3: /* NEG */
            dst0 = newTemp(ty);
            src  = newTemp(ty);
            dst1 = newTemp(ty);
            assign(dst0, mkU(ty,0));
            assign(src,  mkexpr(t1));
            assign(dst1, binop(mkSizedOp(ty,Iop_Sub8),
                               mkexpr(dst0), mkexpr(src)));
            if (locked) {
               casLE( mkexpr(addr), mkexpr(t1)/*expd*/, mkexpr(dst1)/*new*/,
                                    guest_EIP_curr_instr );
            } else {
               storeRealLE( mkexpr(addr),sorb, mkexpr(dst1) );
            }
            setFlags_DEP1_DEP2(Iop_Sub8, dst0, src, ty);
            DIP("neg%c %s\n", nameISize(sz), dis_buf);
            break;
         case 4: /* MUL */
            codegen_mulL_A_D ( sz, False, t1, dis_buf );
            break;
         case 5: /* IMUL */
            codegen_mulL_A_D ( sz, True, t1, dis_buf );
            break;
         case 6: /* DIV */
            codegen_div ( sz, t1, False );
            DIP("div%c %s\n", nameISize(sz), dis_buf);
            break;
         case 7: /* IDIV */
            codegen_div ( sz, t1, True );
            DIP("idiv%c %s\n", nameISize(sz), dis_buf);
            break;
         default: 
            /* This can't happen - gregOfRM should return 0 .. 7 only */
            vpanic("Grp3(x86)");
      }
   }
   return delta;
}


/* Group 4 extended opcodes. */
static
UInt dis_Grp4 ( UChar sorb, Bool locked, Int delta, Bool* decode_OK )
{
   Int   alen;
   UChar modrm;
   HChar dis_buf[50];
   IRType ty = Ity_I8;
   IRTemp t1 = newTemp(ty);
   IRTemp t2 = newTemp(ty);

   *decode_OK = True;

   modrm = getIByte(delta);

   if (locked && (gregOfRM(modrm) != 0 && gregOfRM(modrm) != 1)) {
      /* LOCK prefix only allowed with inc and dec subopcodes */
      *decode_OK = False;
      return delta;
   }

   if (epartIsReg(modrm)) {
      assign(t1, getIReg(1, eregOfRM(modrm)));
      switch (gregOfRM(modrm)) {
         case 0: /* INC */
            assign(t2, binop(Iop_Add8, mkexpr(t1), mkU8(1)));
            putIReg(1, eregOfRM(modrm), mkexpr(t2));
            setFlags_INC_DEC( True, t2, ty );
            break;
         case 1: /* DEC */
            assign(t2, binop(Iop_Sub8, mkexpr(t1), mkU8(1)));
            putIReg(1, eregOfRM(modrm), mkexpr(t2));
            setFlags_INC_DEC( False, t2, ty );
            break;
         default: 
            *decode_OK = False;
            return delta;
      }
      delta++;
      DIP("%sb %s\n", nameGrp4(gregOfRM(modrm)),
                      nameIReg(1, eregOfRM(modrm)));
   } else {
      IRTemp addr = disAMode ( &alen, &sorb, delta, dis_buf );
      assign( t1, loadRealLE(ty,sorb, mkexpr(addr)) );
      switch (gregOfRM(modrm)) {
         case 0: /* INC */
            assign(t2, binop(Iop_Add8, mkexpr(t1), mkU8(1)));
            if (locked) {
               casLE( mkexpr(addr), mkexpr(t1)/*expd*/, mkexpr(t2)/*new*/, 
                      guest_EIP_curr_instr );
            } else {
               storeRealLE( mkexpr(addr),sorb, mkexpr(t2) );
            }
            setFlags_INC_DEC( True, t2, ty );
            break;
         case 1: /* DEC */
            assign(t2, binop(Iop_Sub8, mkexpr(t1), mkU8(1)));
            if (locked) {
               casLE( mkexpr(addr), mkexpr(t1)/*expd*/, mkexpr(t2)/*new*/, 
                      guest_EIP_curr_instr );
            } else {
               storeRealLE( mkexpr(addr),sorb, mkexpr(t2) );
            }
            setFlags_INC_DEC( False, t2, ty );
            break;
         default: 
            *decode_OK = False;
            return delta;
      }
      delta += alen;
      DIP("%sb %s\n", nameGrp4(gregOfRM(modrm)), dis_buf);
   }
   return delta;
}


/* Group 5 extended opcodes. */
static
UInt dis_Grp5 ( UChar sorb, Bool locked, Int sz, Int delta, 
                /*MOD*/DisResult* dres, /*OUT*/Bool* decode_OK )
{
   Int     len;
   UChar   modrm;
   HChar   dis_buf[50];
   IRTemp  addr = IRTemp_INVALID;
   IRType  ty = szToITy(sz);
   IRTemp  t1 = newTemp(ty);
   IRTemp  t2 = IRTemp_INVALID;
   IRTemp  t3;

   *decode_OK = True;

   modrm = getIByte(delta);

   if (locked && (gregOfRM(modrm) != 0 && gregOfRM(modrm) != 1)) {
      /* LOCK prefix only allowed with inc and dec subopcodes */
      *decode_OK = False;
      return delta;
   }

   if (epartIsReg(modrm)) {
      assign(t1, getIReg(sz,eregOfRM(modrm)));
      switch (gregOfRM(modrm)) {
         case 0: /* INC */ 
            vassert(sz == 2 || sz == 4);
            t2 = newTemp(ty);
            assign(t2, binop(mkSizedOp(ty,Iop_Add8),
                             mkexpr(t1), mkU(ty,1)));
            setFlags_INC_DEC( True, t2, ty );
            putIReg(sz,eregOfRM(modrm),mkexpr(t2));
            break;
         case 1: /* DEC */ 
            vassert(sz == 2 || sz == 4);
            t2 = newTemp(ty);
            assign(t2, binop(mkSizedOp(ty,Iop_Sub8),
                             mkexpr(t1), mkU(ty,1)));
            setFlags_INC_DEC( False, t2, ty );
            putIReg(sz,eregOfRM(modrm),mkexpr(t2));
            break;
         case 2: /* call Ev */
            t2 = newTemp(Ity_I32);
            assign(t2, binop(Iop_Sub32, getIReg(4,R_ESP), mkU32(2)));
            putIReg(4, R_ESP, mkexpr(t2));
            storeRealLE( mkexpr(t2),R_SS, mkU32(fix_ip(guest_EIP_bbstart+delta+1)));
            jmp_treg(dres, Ijk_Call, t1);
            vassert(dres->whatNext == Dis_StopHere);
            break;
         case 3: /* callf EV */
            vassert("not yet supported");
         case 4: /* jmp Ev */
            vassert(sz == 4 || sz == 2);
            t3 = newTemp(Ity_I32);
            assign(t3, realAddr(getSReg(R_CS), mkexpr(t1)));
            jmp_treg(dres, Ijk_Boring, t3);
            vassert(dres->whatNext == Dis_StopHere);
            break;
         case 5: /* jmpf EV */
            vassert("not yet supported");
         case 6: /* PUSH Ev */
            vassert(sz == 4 || sz == 2);
            t2 = newTemp(Ity_I32);
            assign( t2, binop(Iop_Sub32,getIReg(4,R_ESP),mkU32(sz)) );
            putIReg(4, R_ESP, mkexpr(t2) );
            storeRealLE( mkexpr(t2),R_SS, mkexpr(t1) );
            break;
         default: 
            *decode_OK = False;
            return delta;
      }
      delta++;
      DIP("%s%c %s\n", nameGrp5(gregOfRM(modrm)),
                       nameISize(sz), nameIReg(sz, eregOfRM(modrm)));
   } else {
      addr = disAMode ( &len, &sorb, delta, dis_buf );
      assign(t1, loadRealLE(ty,sorb, mkexpr(addr)));
      switch (gregOfRM(modrm)) {
         case 0: /* INC */ 
            t2 = newTemp(ty);
            assign(t2, binop(mkSizedOp(ty,Iop_Add8),
                             mkexpr(t1), mkU(ty,1)));
            if (locked) {
               casLE( mkexpr(addr),
                      mkexpr(t1), mkexpr(t2), guest_EIP_curr_instr );
            } else {
               storeRealLE(mkexpr(addr), sorb,mkexpr(t2));
            }
            setFlags_INC_DEC( True, t2, ty );
            break;
         case 1: /* DEC */ 
            t2 = newTemp(ty);
            assign(t2, binop(mkSizedOp(ty,Iop_Sub8),
                             mkexpr(t1), mkU(ty,1)));
            if (locked) {
               casLE( mkexpr(addr),
                      mkexpr(t1), mkexpr(t2), guest_EIP_curr_instr );
            } else {
               storeRealLE(mkexpr(addr),sorb,mkexpr(t2));
            }
            setFlags_INC_DEC( False, t2, ty );
            break;
         case 2: /* call Ev */
            vassert(sz == 4);
            t2 = newTemp(Ity_I32);
            assign(t2, binop(Iop_Sub32, getIReg(4,R_ESP), mkU32(4)));
            putIReg(4, R_ESP, mkexpr(t2));
            storeRealLE( mkexpr(t2),R_SS, mkU32(fix_ip(guest_EIP_bbstart+delta+len)));
            jmp_treg(dres, Ijk_Call, t1);
            vassert(dres->whatNext == Dis_StopHere);
            break;
         case 3: /* callf EV */
            vassert("not yet supported");
         case 4: /* JMP Ev */
            vassert(sz == 2);
            t3 = newTemp(Ity_I32);
            assign(t3, realAddr(getSReg(R_CS), mkexpr(t1)));
            jmp_treg(dres, Ijk_Boring, t3);
            vassert(dres->whatNext == Dis_StopHere);
            break;
         case 5: /* jmpf EV */
            vassert("not yet supported");
         case 6: /* PUSH Ev */
            vassert(sz == 4 || sz == 2);
            t2 = newTemp(Ity_I32);
            assign( t2, binop(Iop_Sub32,getIReg(4,R_ESP),mkU32(sz)) );
            putIReg(4, R_ESP, mkexpr(t2) );
            storeRealLE( mkexpr(t2),R_SS, mkexpr(t1) );
            break;
         default: 
            *decode_OK = False;
            return delta;
      }
      delta += len;
      DIP("%s%c %s\n", nameGrp5(gregOfRM(modrm)),
                       nameISize(sz), dis_buf);
   }
   return delta;
}



/* Move 16 bits from Ew (ireg or mem) to G (a segment register). */

static
UInt dis_mov_Ew_Sw ( UChar sorb, Int delta0 )
{
   Int    len;
   IRTemp addr;
   UChar  rm  = getIByte(delta0);
   HChar  dis_buf[50];

   if (epartIsReg(rm)) {
      putSReg( gregOfRM(rm), getIReg(2, eregOfRM(rm)) );
      DIP("movw %s,%s\n", nameIReg(2,eregOfRM(rm)), nameSReg(gregOfRM(rm)));
      return 1+delta0;
   } else {
      addr = disAMode ( &len, &sorb, delta0, dis_buf );
      putSReg( gregOfRM(rm), loadRealLE(Ity_I16,sorb, mkexpr(addr)));
      DIP("movw %s,%s\n", dis_buf, nameSReg(gregOfRM(rm)));
      return len+delta0;
   }
}

static
UInt dis_mov_Sw_Ew ( UChar sorb,
                     Int   sz,
                     Int   delta0 )
{
   Int    len;
   IRTemp addr;
   UChar  rm  = getIByte(delta0);
   HChar  dis_buf[50];

   vassert(sz == 2);

   if (epartIsReg(rm)) {
      putIReg(2, eregOfRM(rm), getSReg(gregOfRM(rm)));
      DIP("mov %s,%s\n", nameSReg(gregOfRM(rm)), nameIReg(sz,eregOfRM(rm)));
      return 1+delta0;
   } else {
      addr = disAMode ( &len, &sorb, delta0, dis_buf );
      storeRealLE( mkexpr(addr),sorb,  getSReg(gregOfRM(rm)));
      DIP("mov %s,%s\n", nameSReg(gregOfRM(rm)), dis_buf);
      return len+delta0;
   }
}

static
UInt dis_mov_E_G ( UChar       sorb,
                   Int         size, 
                   Int         delta0 )
{
   Int len;
   UChar rm = getIByte(delta0);
   HChar dis_buf[50];

   if (epartIsReg(rm)) {
      putIReg(size, gregOfRM(rm), getIReg(size, eregOfRM(rm)));
      DIP("mov%c %s,%s\n", nameISize(size), 
                           nameIReg(size,eregOfRM(rm)),
                           nameIReg(size,gregOfRM(rm)));
      return 1+delta0;
   }

   /* E refers to memory */    
   {
      IRTemp addr = disAMode ( &len, &sorb, delta0, dis_buf );
      putIReg(size, gregOfRM(rm), loadRealLE(szToITy(size), sorb, mkexpr(addr)));
      DIP("mov%c %s,%s\n", nameISize(size), 
                           dis_buf,nameIReg(size,gregOfRM(rm)));
      return delta0+len;
   }
}

static
UInt dis_mov_G_E ( UChar       sorb,
                   Int         size, 
                   Int         delta0 )
{
   Int len;
   UChar rm = getIByte(delta0);
   HChar dis_buf[50];

   if (epartIsReg(rm)) {
      putIReg(size, eregOfRM(rm), getIReg(size, gregOfRM(rm)));
      DIP("mov%c %s,%s\n", nameISize(size), 
                           nameIReg(size,gregOfRM(rm)),
                           nameIReg(size,eregOfRM(rm)));
      return 1+delta0;
   }

   /* E refers to memory */    
   {
      IRTemp addr = disAMode ( &len, &sorb, delta0, dis_buf);
      storeRealLE(mkexpr(addr), sorb ,getIReg(size, gregOfRM(rm)));
      DIP("mov%c %s,%s\n", nameISize(size), 
                           nameIReg(size,gregOfRM(rm)), dis_buf);
      return len+delta0;
   }
}

static
UInt dis_imul_I_E_G ( UChar       sorb,
                      Int         size, 
                      Int         delta,
                      Int         litsize )
{
   Int    d32, alen;
   HChar  dis_buf[50];
   UChar  rm = getIByte(delta);
   IRTemp te = newTemp(Ity_I16);
   IRTemp tl = newTemp(Ity_I16);
   IRTemp resLo = newTemp(Ity_I16);

   if (epartIsReg(rm)) {
      assign(te, getIReg(2, eregOfRM(rm)));
      delta++;
   } else {
      IRTemp addr = disAMode( &alen, &sorb, delta, dis_buf );
      assign(te, loadRealLE(Ity_I16, sorb ,mkexpr(addr)));
      delta += alen;
   }
   d32 = getSDisp(litsize,delta);
   delta += litsize;

   assign(tl, mkU(Ity_I16,d32));

   assign( resLo, binop( Iop_Mul16, mkexpr(te), mkexpr(tl) ));

   setFlags_MUL ( Ity_I16, te, tl, X86G_CC_OP_SMULB );

   putIReg(2, gregOfRM(rm), mkexpr(resLo));

   DIP("imul %d, %s, %s\n", d32, 
       ( epartIsReg(rm) ? nameIReg(size,eregOfRM(rm)) : dis_buf ),
       nameIReg(size,gregOfRM(rm)) );
   return delta;
}

static 
void codegen_xchg_eAX_Reg ( Int sz, Int reg )
{
   IRType ty = szToITy(sz);
   IRTemp t1 = newTemp(ty);
   IRTemp t2 = newTemp(ty);
   vassert(sz == 2 || sz == 4);
   assign( t1, getIReg(sz, R_EAX) );
   assign( t2, getIReg(sz, reg) );
   putIReg( sz, R_EAX, mkexpr(t2) );
   putIReg( sz, reg, mkexpr(t1) );
   DIP("xchg%c %s, %s\n", 
       nameISize(sz), nameIReg(sz, R_EAX), nameIReg(sz, reg));
}

static 
void codegen_SAHF ( void )
{
   /* Set the flags to:
      (x86g_calculate_flags_all() & X86G_CC_MASK_O)  -- retain the old O flag
      | (%AH & (X86G_CC_MASK_S|X86G_CC_MASK_Z|X86G_CC_MASK_A
                |X86G_CC_MASK_P|X86G_CC_MASK_C)
   */
   UInt   mask_SZACP = X86G_CC_MASK_S|X86G_CC_MASK_Z|X86G_CC_MASK_A
                       |X86G_CC_MASK_C|X86G_CC_MASK_P;
   IRTemp oldflags   = newTemp(Ity_I32);
   assign( oldflags, mk_x86g_calculate_eflags_all() );
   stmt( IRStmt_Put( OFFB_CC_OP,   mkU32(X86G_CC_OP_COPY) ));
   stmt( IRStmt_Put( OFFB_CC_NDEP, mkU32(0) ));
   stmt( IRStmt_Put( OFFB_CC_DEP2, mkU32(0) ));
   stmt( IRStmt_Put( OFFB_CC_DEP1,
         binop(Iop_Or32,
               binop(Iop_And32, mkexpr(oldflags), mkU32(X86G_CC_MASK_O)),
               binop(Iop_And32, 
                     binop(Iop_Shr32, getIReg(4, R_EAX), mkU8(8)),
                     mkU32(mask_SZACP))
              )
   ));
   /* Set NDEP even though it isn't used.  This makes redundant-PUT
      elimination of previous stores to this field work better. */
   stmt( IRStmt_Put( OFFB_CC_NDEP, mkU32(0) ));
}


static 
void codegen_LAHF ( void  )
{
   /* AH <- EFLAGS(SF:ZF:0:AF:0:PF:1:CF) */
   IRExpr* eax_with_hole;
   IRExpr* new_byte;
   IRExpr* new_eax;
   UInt    mask_SZACP = X86G_CC_MASK_S|X86G_CC_MASK_Z|X86G_CC_MASK_A
                        |X86G_CC_MASK_C|X86G_CC_MASK_P;

   IRTemp  flags = newTemp(Ity_I32);
   assign( flags, mk_x86g_calculate_eflags_all() );

   eax_with_hole 
      = binop(Iop_And32, getIReg(4, R_EAX), mkU32(0xFFFF00FF));
   new_byte 
      = binop(Iop_Or32, binop(Iop_And32, mkexpr(flags), mkU32(mask_SZACP)),
                        mkU32(1<<1));
   new_eax 
      = binop(Iop_Or32, eax_with_hole,
                        binop(Iop_Shl32, new_byte, mkU8(8)));
   putIReg(4, R_EAX, new_eax);
}

static 
void dis_push_segreg ( UInt sreg, Int sz )
{
    IRTemp t1 = newTemp(Ity_I16);
    IRTemp ta = newTemp(Ity_I32);
    vassert(sz == 2);

    assign( t1, getSReg(sreg) );
    assign( ta, binop(Iop_Sub32, getIReg(4, R_ESP), mkU32(sz)) );
    putIReg(4, R_ESP, mkexpr(ta));
    storeRealLE( mkexpr(ta),R_SS, mkexpr(t1) );

    DIP("push%c %s\n", sz==2 ? 'w' : 'l', nameSReg(sreg));
}


static
void dis_pop_segreg ( UInt sreg, Int sz )
{
    IRTemp t1 = newTemp(Ity_I16);
    IRTemp ta = newTemp(Ity_I32);
    vassert(sz == 2);

    assign( ta, getIReg(4, R_ESP) );
    assign( t1, loadRealLE(Ity_I16, R_SS, mkexpr(ta)) );

    putIReg(4, R_ESP, binop(Iop_Add32, mkexpr(ta), mkU32(sz)) );
    putSReg( sreg, mkexpr(t1) );
    DIP("pop%c %s\n", sz==2 ? 'w' : 'l', nameSReg(sreg));
}

/* Helper for deciding whether a given insn (starting at the opcode
   byte) may validly be used with a LOCK prefix.  The following insns
   may be used with LOCK when their destination operand is in memory.
   AFAICS this is exactly the same for both 32-bit and 64-bit mode.

   ADD        80 /0,  81 /0,  82 /0,  83 /0,  00,  01
   OR         80 /1,  81 /1,  82 /x,  83 /1,  08,  09
   ADC        80 /2,  81 /2,  82 /2,  83 /2,  10,  11
   SBB        81 /3,  81 /3,  82 /x,  83 /3,  18,  19
   AND        80 /4,  81 /4,  82 /x,  83 /4,  20,  21
   SUB        80 /5,  81 /5,  82 /x,  83 /5,  28,  29
   XOR        80 /6,  81 /6,  82 /x,  83 /6,  30,  31

   DEC        FE /1,  FF /1
   INC        FE /0,  FF /0

   NEG        F6 /3,  F7 /3
   NOT        F6 /2,  F7 /2

   XCHG       86, 87

   BTC        0F BB,  0F BA /7
   BTR        0F B3,  0F BA /6
   BTS        0F AB,  0F BA /5

   CMPXCHG    0F B0,  0F B1
   CMPXCHG8B  0F C7 /1

   XADD       0F C0,  0F C1

   ------------------------------

   80 /0  =  addb $imm8,  rm8
   81 /0  =  addl $imm32, rm32  and  addw $imm16, rm16
   82 /0  =  addb $imm8,  rm8
   83 /0  =  addl $simm8, rm32  and  addw $simm8, rm16

   00     =  addb r8,  rm8
   01     =  addl r32, rm32  and  addw r16, rm16

   Same for ADD OR ADC SBB AND SUB XOR

   FE /1  = dec rm8
   FF /1  = dec rm32  and  dec rm16

   FE /0  = inc rm8
   FF /0  = inc rm32  and  inc rm16

   F6 /3  = neg rm8
   F7 /3  = neg rm32  and  neg rm16

   F6 /2  = not rm8
   F7 /2  = not rm32  and  not rm16

   0F BB     = btcw r16, rm16    and  btcl r32, rm32
   OF BA /7  = btcw $imm8, rm16  and  btcw $imm8, rm32

   Same for BTS, BTR
*/
static Bool can_be_used_with_LOCK_prefix ( const UChar* opc )
{
   switch (opc[0]) {
      case 0x00: case 0x01: case 0x08: case 0x09:
      case 0x10: case 0x11: case 0x18: case 0x19:
      case 0x20: case 0x21: case 0x28: case 0x29:
      case 0x30: case 0x31:
         if (!epartIsReg(opc[1]))
            return True;
         break;

      case 0x80: case 0x81: case 0x82: case 0x83:
         if (gregOfRM(opc[1]) >= 0 && gregOfRM(opc[1]) <= 6
             && !epartIsReg(opc[1]))
            return True;
         break;

      case 0xFE: case 0xFF:
         if (gregOfRM(opc[1]) >= 0 && gregOfRM(opc[1]) <= 1
             && !epartIsReg(opc[1]))
            return True;
         break;

      case 0xF6: case 0xF7:
         if (gregOfRM(opc[1]) >= 2 && gregOfRM(opc[1]) <= 3
             && !epartIsReg(opc[1]))
            return True;
         break;

      case 0x86: case 0x87:
         if (!epartIsReg(opc[1]))
            return True;
         break;

      case 0x0F: {
         switch (opc[1]) {
            case 0xBB: case 0xB3: case 0xAB:
               if (!epartIsReg(opc[2]))
                  return True;
               break;
            case 0xBA: 
               if (gregOfRM(opc[2]) >= 5 && gregOfRM(opc[2]) <= 7
                   && !epartIsReg(opc[2]))
                  return True;
               break;
            case 0xB0: case 0xB1:
               if (!epartIsReg(opc[2]))
                  return True;
               break;
            case 0xC7: 
               if (gregOfRM(opc[2]) == 1 && !epartIsReg(opc[2]) )
                  return True;
               break;
            case 0xC0: case 0xC1:
               if (!epartIsReg(opc[2]))
                  return True;
               break;
            default:
               break;
         } /* switch (opc[1]) */
         break;
      }

      default:
         break;
   } /* switch (opc[0]) */

   return False;
}


static
void dis_ret ( /*MOD*/DisResult* dres, UInt d32, Bool is_far )
{
    IRTemp tSP = newTemp(Ity_I16);
    IRTemp tIP = newTemp(Ity_I16);
    IRTemp tCS_IP = newTemp(Ity_I32);
    IRTemp tCS = newTemp(Ity_I16);;
    assign(tSP, getIReg(2, R_ESP));
    assign(tIP, loadRealLE(Ity_I16,R_SS,mkexpr(tSP)));
    if (is_far){
      assign(tCS, loadRealLE(Ity_I16, R_SS ,binop(Iop_Add16,mkexpr(tSP),mkU16(2))));
      putSReg(R_CS, mkexpr(tCS));
    }
    else {
       assign(tCS, getSReg(R_CS));
    }
    putIReg(2, R_ESP,binop(Iop_Add16, mkexpr(tSP), mkU16((is_far?4:2)+d32)));
    assign(tCS_IP, realAddr(mkexpr(tCS), mkexpr(tIP)));
    jmp_treg(dres, Ijk_Ret, tCS_IP);
    vassert(dres->whatNext == Dis_StopHere);
}


/*------------------------------------------------------------*/
/*--- Disassemble a single instruction                     ---*/
/*------------------------------------------------------------*/

/* Disassemble a single instruction into IR.  The instruction is
   located in host memory at &guest_code[delta].  *expect_CAS is set
   to True if the resulting IR is expected to contain an IRCAS
   statement, and False if it's not expected to.  This makes it
   possible for the caller of disInstr_8086_WRK to check that
   LOCK-prefixed instructions are at least plausibly translated, in
   that it becomes possible to check that a (validly) LOCK-prefixed
   instruction generates a translation containing an IRCAS, and
   instructions without LOCK prefixes don't generate translations
   containing an IRCAS.
*/
static
DisResult disInstr_8086_WRK (
             /*OUT*/Bool* expect_CAS,
             Bool         (*resteerOkFn) ( /*opaque*/void*, Addr ),
             Bool         resteerCisOk,
             void*        callback_opaque,
             Long         delta64,
             const VexArchInfo* archinfo,
             const VexAbiInfo*  vbi,
             Bool         sigill_diag
          )
{
   IRType    ty;
   IRTemp    addr, t0, t1, t2, t3, t4, t5, t6;
   Int       alen;
   UChar     opc, modrm, abyte, pre;
   UInt      d32, c32;
   HChar     dis_buf[50];
   Int       am_sz, d_sz, n_prefixes;
   DisResult dres;
   const UChar* insn; /* used in SSE decoders */
   Bool      has_66_pfx = 0;

   /* The running delta */
   Int delta = (Int)delta64;

   /* Holds eip at the start of the insn, so that we can print
      consistent error messages for unimplemented insns. */
   Int delta_start = delta;

   /* we keep using sz in order to avoid changing a lot of code without
    * any gain. So sz is equal to the current_sz_data.
    */
   Int sz = 2;

   /* sorb holds the segment-override-prefix byte, if any.  Zero if no
      prefix has been seen, else one of {0x26, 0x36, 0x3E, 0x64, 0x65}
      indicating the prefix.  */
   UChar sorb = UNDEFINED_SEG;

   /* Gets set to True if a LOCK prefix is seen. */
   Bool pfx_lock = False;

   /* Set result defaults. */
   dres.whatNext    = Dis_Continue;
   dres.len         = 0;
   dres.continueAt  = 0;
   dres.jk_StopHere = Ijk_INVALID;

   *expect_CAS = False;

   addr = t0 = t1 = t2 = t3 = t4 = t5 = t6 = IRTemp_INVALID; 
   vassert(guest_EIP_bbstart + delta == guest_EIP_curr_instr); // TODO this is not correct in the case of 8086
   DIP("\t0x%x:  ", guest_EIP_bbstart+delta);       

   /* Normal instruction handling starts here. */

   /* Deal with some but not all prefixes: 
         F0(lock)
         2E(cs:) 3E(ds:) 26(es:) 64(fs:) 65(gs:) 36(ss:)
      Not dealt with (left in place):
         F2 F3
   */
   n_prefixes = 0;
   while (True) {
      if (n_prefixes > 7) goto decode_failure;
      pre = getUChar(delta);
      switch (pre) {
         case 0xF0: 
            pfx_lock = True; 
            *expect_CAS = True;
            break;
         case 0x3E: /* %DS: */
         if (sorb != UNDEFINED_SEG) 
               goto decode_failure; /* only one seg override allowed */
            sorb = EXPLICIT_BIT | R_DS;
            break;
         case 0x26: /* %ES: */
         if (sorb != UNDEFINED_SEG) 
               goto decode_failure; /* only one seg override allowed */
            sorb = EXPLICIT_BIT | R_ES;
            break;
         case 0x36: /* %SS: */
            if (sorb != UNDEFINED_SEG) 
               goto decode_failure; /* only one seg override allowed */
            sorb = EXPLICIT_BIT | R_SS;
            break;
         case 0x2E: { /* %CS: */
            /* 2E prefix on a conditional branch instruction is a
               branch-prediction hint, which can safely be ignored.  */
            UChar op1 = getIByte(delta+1);
            UChar op2 = getIByte(delta+2);
            if ((op1 >= 0x70 && op1 <= 0x7F)
                || (op1 == 0xE3)
                || (op1 == 0x0F && op2 >= 0x80 && op2 <= 0x8F)) {
               if (0) vex_printf("vex x86->IR: ignoring branch hint\n");
            } else {
              sorb = EXPLICIT_BIT | R_CS;
            }
            break;
         }
         default: 
            goto not_a_prefix;
      }
      n_prefixes++;
      delta++;
   }

   not_a_prefix:

   /* Now we should be looking at the primary opcode byte or the
      leading F2 or F3.  Check that any LOCK prefix is actually
      allowed. */

   if (pfx_lock) {
     if (can_be_used_with_LOCK_prefix( &guest_code[delta] )) {
         DIP("lock ");
      } else {
         *expect_CAS = False;
         goto decode_failure;
      }
   }




   /* ---------------------------------------------------- */
   /* --- start of the baseline insn decoder            -- */
   /* ---------------------------------------------------- */

   /* Get the primary opcode. */
   opc = getIByte(delta); delta++;

   /* We get here if the current insn isn't SSE, or this CPU doesn't
      support SSE. */

   switch (opc) {

   /* ------------------------ Control flow --------------- */


   case 0xC2: /* RET imm16 */
   case 0xCA: /* RETF imm16 */
   case 0xC3: /* RET */
   case 0xCB: /* RETF */
   {
    Bool far = is_bit_set(opc, 3);
    Bool disp = !is_bit_set(opc, 0);
      if(disp){
          d32 = getSDisp16(delta);
          delta += 2;
        }
      dis_ret(&dres, (disp ? d32 : 0), far);
   }
   case 0xCF: /* IRET */
      /* Note, this is an extremely kludgey and limited implementation
         of iret.  All it really does is: 
            popl %EIP; popl %CS; popl %EFLAGS.
         %CS is set but ignored (as it is in (eg) popw %cs)". */
         /* 8086 shoul dhave fixed it, but who knows.. */
      t1 = newTemp(Ity_I16); /* SP content */
      t2 = newTemp(Ity_I16); /* new EIP */
      t3 = newTemp(Ity_I16); /* new CS */
      t4 = newTemp(Ity_I16); /* new EFLAGS */
      t5 = newTemp(Ity_I32); /* real return address */
      assign(t1, getIReg(2, R_ESP));
      assign(t2, loadRealLE(Ity_I16, R_SS, binop(Iop_Add16,mkexpr(t1),mkU32(0))));
      assign(t3, loadRealLE(Ity_I16, R_SS, binop(Iop_Add16,mkexpr(t1),mkU32(2))));
      assign(t4, loadRealLE(Ity_I16, R_SS, binop(Iop_Add16,mkexpr(t1),mkU32(4))));
      /* Get stuff off stack */
      putIReg(2, R_ESP,binop(Iop_Add16, mkexpr(t1), mkU32(6)));
      /* set %CS (which is ignored anyway) */
      putSReg(R_CS, mkexpr(t3));
      /* set %EFLAGS */
      set_EFLAGS_from_value( t4, False/*!emit_AC_emwarn*/, 0/*unused*/ );
      /* goto new EIP value */
      assign(t5, realAddr(mkexpr(t3),mkexpr(t2)));
      jmp_treg(&dres, Ijk_Ret, t5);
      vassert(dres.whatNext == Dis_StopHere);
      DIP("iret (not so kludgey)\n");
      break;

   case 0x9A: /* CALL FAR ABS */
      c32 = getUDisp16(delta); delta += 2;
      d32 = getSDisp16(delta); delta += 2;
      t1 = newTemp(Ity_I16);
      t2 = newTemp(Ity_I16);
      t3 = newTemp(Ity_I16);
      t4 = newTemp(Ity_I32);
      assign(t1, getIReg(2,R_ESP));
      assign(t2, binop(Iop_Sub16, mkexpr(t1), mkU16(2)));
      assign(t3, binop(Iop_Sub16, mkexpr(t1), mkU16(4)));

      storeRealLE( mkexpr(t2), R_SS , getSReg(R_CS));
      storeRealLE( mkexpr(t3), R_SS , mkU16(guest_EIP_bbstart+delta));
      
      putIReg(2, R_ESP, mkexpr(t3));
      assign(t4, realAddr(mkU16(c32),mkU16(d32)));

      jmp_treg(&dres, Ijk_Call, t4);
      vassert(dres.whatNext == Dis_StopHere);
      DIP("call far 0x%x:0x%x\n",c32, d32);
      break;


   case 0xE8: /* CALL NEAR REL*/

      d32 = getSDisp16(delta); delta += 2;
      d32 += (guest_EIP_bbstart+delta); 
      d32 = fix_ip(d32);
      /* The normal sequence for a call. */
       t1 = newTemp(Ity_I16); 
         assign(t1, binop(Iop_Sub32, getIReg(2,R_ESP), mkU32(2)));
         putIReg(2, R_ESP, mkexpr(t1));
         storeRealLE( mkexpr(t1), R_SS, mkU32(guest_EIP_bbstart+delta));
         if (resteerOkFn( callback_opaque, (Addr32)d32 )) {
            /* follow into the call target. */
            dres.whatNext   = Dis_ResteerU;
            dres.continueAt = (Addr32)d32;
         } else {
            jmp_lit(&dres, Ijk_Call, d32);
            vassert(dres.whatNext == Dis_StopHere);
         }
      DIP("call 0x%x\n",d32);
      break;



   case 0xC9: /* LEAVE */
      t1 = newTemp(Ity_I16); t2 = newTemp(Ity_I16);
      assign(t1, getIReg(2,R_EBP));
      /* First PUT ESP looks redundant, but need it because ESP must
         always be up-to-date for Memcheck to work... */
      putIReg(2, R_ESP, mkexpr(t1));
      assign(t2, loadRealLE(Ity_I16,R_SS,mkexpr(t1)));
      putIReg(2, R_EBP, mkexpr(t2));
      putIReg(2, R_ESP, binop(Iop_Add32, mkexpr(t1), mkU16(2)) );
      DIP("leave\n");
      break;

   /* ---------------- Misc weird-ass insns --------------- */
   /* currently unsupported, check later if we really need to get into this one.. */
   case 0x27: /* DAA */
   case 0x2F: /* DAS */
   case 0x37: /* AAA */
   case 0x3F: /* AAS */
      /* An ugly implementation for some ugly instructions.  Oh
	 well. */
      if (sz != 4) goto decode_failure;
      t1 = newTemp(Ity_I32);
      t2 = newTemp(Ity_I32);
      /* Make up a 32-bit value (t1), with the old value of AX in the
         bottom 16 bits, and the old OSZACP bitmask in the upper 16
         bits. */
      assign(t1, 
             binop(Iop_16HLto32, 
                   unop(Iop_32to16,
                        mk_x86g_calculate_eflags_all()),
                   getIReg(2, R_EAX)
            ));
      /* Call the helper fn, to get a new AX and OSZACP value, and
         poke both back into the guest state.  Also pass the helper
         the actual opcode so it knows which of the 4 instructions it
         is doing the computation for. */
      vassert(opc == 0x27 || opc == 0x2F || opc == 0x37 || opc == 0x3F);
      assign(t2,
              mkIRExprCCall(
                 Ity_I32, 0/*regparm*/, "x86g_calculate_daa_das_aaa_aas",
                 &x86g_calculate_daa_das_aaa_aas,
                 mkIRExprVec_2( mkexpr(t1), mkU32( opc & 0xFF) )
            ));
     putIReg(2, R_EAX, unop(Iop_32to16, mkexpr(t2) ));

     stmt( IRStmt_Put( OFFB_CC_OP,   mkU32(X86G_CC_OP_COPY) ));
     stmt( IRStmt_Put( OFFB_CC_DEP2, mkU32(0) ));
     stmt( IRStmt_Put( OFFB_CC_DEP1, 
                       binop(Iop_And32,
                             binop(Iop_Shr32, mkexpr(t2), mkU8(16)),
                             mkU32( X86G_CC_MASK_C | X86G_CC_MASK_P 
                                    | X86G_CC_MASK_A | X86G_CC_MASK_Z 
                                    | X86G_CC_MASK_S| X86G_CC_MASK_O )
                            )
                      )
         );
     /* Set NDEP even though it isn't used.  This makes redundant-PUT
        elimination of previous stores to this field work better. */
     stmt( IRStmt_Put( OFFB_CC_NDEP, mkU32(0) ));
     switch (opc) {
        case 0x27: DIP("daa\n"); break;
        case 0x2F: DIP("das\n"); break;
        case 0x37: DIP("aaa\n"); break;
        case 0x3F: DIP("aas\n"); break;
        default: vassert(0);
     }
     break;

   case 0xD4: /* AAM */
   case 0xD5: /* AAD */
      d32 = getIByte(delta); delta++;
      if (sz != 4 || d32 != 10) goto decode_failure;
      t1 = newTemp(Ity_I32);
      t2 = newTemp(Ity_I32);
      /* Make up a 32-bit value (t1), with the old value of AX in the
         bottom 16 bits, and the old OSZACP bitmask in the upper 16
         bits. */
      assign(t1, 
             binop(Iop_16HLto32, 
                   unop(Iop_32to16,
                        mk_x86g_calculate_eflags_all()),
                   getIReg(2, R_EAX)
            ));
      /* Call the helper fn, to get a new AX and OSZACP value, and
         poke both back into the guest state.  Also pass the helper
         the actual opcode so it knows which of the 2 instructions it
         is doing the computation for. */
      assign(t2,
              mkIRExprCCall(
                 Ity_I32, 0/*regparm*/, "x86g_calculate_aad_aam",
                 &x86g_calculate_aad_aam,
                 mkIRExprVec_2( mkexpr(t1), mkU32( opc & 0xFF) )
            ));
      putIReg(2, R_EAX, unop(Iop_32to16, mkexpr(t2) ));

      stmt( IRStmt_Put( OFFB_CC_OP,   mkU32(X86G_CC_OP_COPY) ));
      stmt( IRStmt_Put( OFFB_CC_DEP2, mkU32(0) ));
      stmt( IRStmt_Put( OFFB_CC_DEP1, 
                        binop(Iop_And32,
                              binop(Iop_Shr32, mkexpr(t2), mkU8(16)),
                              mkU32( X86G_CC_MASK_C | X86G_CC_MASK_P 
                                     | X86G_CC_MASK_A | X86G_CC_MASK_Z 
                                     | X86G_CC_MASK_S| X86G_CC_MASK_O )
                             )
                       )
          );
      /* Set NDEP even though it isn't used.  This makes
         redundant-PUT elimination of previous stores to this field
         work better. */
      stmt( IRStmt_Put( OFFB_CC_NDEP, mkU32(0) ));

      DIP(opc == 0xD4 ? "aam\n" : "aad\n");
      break;

   /* ------------------------ CWD/CDQ -------------------- */

   case 0x98: /* CBW */
      putIReg(2, R_EAX, unop(Iop_8Sto16, getIReg(1, R_EAX)));
      DIP("cbw\n");
      break;

   /* ----------------------- FLAG ops -------------------- */   

   case 0x9E: /* SAHF */
      codegen_SAHF();
      DIP("sahf\n");
      break;

   case 0x9F: /* LAHF */
      codegen_LAHF();
      DIP("lahf\n");
      break;

   /* ------------------------ FPU ops -------------------- */
   /* currently unsupported, check later if we really need to get into this one.. */
   case 0xD8:
   case 0xD9:
   case 0xDA:
   case 0xDB:
   case 0xDC:
   case 0xDD:
   case 0xDE:
   case 0xDF: 
   
   goto decode_failure;
   {
      Int  delta0    = delta;
      Bool decode_OK = False;
      delta = dis_FPU ( &decode_OK, sorb, delta );
      if (!decode_OK) {
         delta = delta0;
         goto decode_failure;
      }
      break;
   }

   /* ------------------------ INC & DEC ------------------ */

   case 0x40: /* INC eAX */
   case 0x41: /* INC eCX */
   case 0x42: /* INC eDX */
   case 0x43: /* INC eBX */
   case 0x44: /* INC eSP */
   case 0x45: /* INC eBP */
   case 0x46: /* INC eSI */
   case 0x47: /* INC eDI */
      t1 = newTemp(Ity_I16);
      assign( t1, binop(Iop_Add16,
                        getIReg(2, (UInt)(opc - 0x40)),
                        mkU(Ity_I16,1)) );
      setFlags_INC_DEC( True, t1, Ity_I16 );
      putIReg(2, (UInt)(opc - 0x40), mkexpr(t1));
      DIP("inc%c %s\n", nameISize(2), nameIReg(2,opc-0x40));
      break;

   case 0x48: /* DEC eAX */
   case 0x49: /* DEC eCX */
   case 0x4A: /* DEC eDX */
   case 0x4B: /* DEC eBX */
   case 0x4C: /* DEC eSP */
   case 0x4D: /* DEC eBP */
   case 0x4E: /* DEC eSI */
   case 0x4F: /* DEC eDI */
      t1 = newTemp(Ity_I16);
      assign( t1, binop(Iop_Sub16,
                        getIReg(2, (UInt)(opc - 0x48)),
                        mkU(Ity_I16,1)) );
      setFlags_INC_DEC( False, t1, Ity_I16 );
      putIReg(2, (UInt)(opc - 0x48), mkexpr(t1));
      DIP("dec%c %s\n", nameISize(2), nameIReg(2,opc-0x48));
      break;

   /* ------------------------ INT ------------------------ */

   case 0xCC: /* INT 3 */
      jmp_lit(&dres, Ijk_SigTRAP,  (Addr32)fix_ip(guest_EIP_bbstart+delta));
      vassert(dres.whatNext == Dis_StopHere);
      DIP("int $0x3\n");
      break;

   case 0xCD: /* INT imm8 */
      d32 = getIByte(delta); delta++;

      /* For any of the cases where we emit a jump (that is, for all
         currently handled cases), it's important that all ArchRegs
         carry their up-to-date value at this point.  So we declare an
         end-of-block here, which forces any TempRegs caching ArchRegs
         to be flushed. */

      /* Handle int $0x3F .. $0x4F by synthesising a segfault and a
         restart of this instruction (hence the "-2" two lines below,
         to get the restart EIP to be this instruction.  This is
         probably Linux-specific and it would be more correct to only
         do this if the VexAbiInfo says that is what we should do.
         This used to handle just 0x40-0x43; Jikes RVM uses a larger
         range (0x3F-0x49), and this allows some slack as well. */
      if (d32 >= 0x3F && d32 <= 0x4F) {
         jmp_lit(&dres, Ijk_SigSEGV, (Addr32)fix_ip(guest_EIP_bbstart+delta-2));
         vassert(dres.whatNext == Dis_StopHere);
         DIP("int $0x%x\n", d32);
         break;
      }

      /* Handle int $0x80 (linux syscalls), int $0x81 and $0x82
         (darwin syscalls), int $0x91 (Solaris syscalls) and int $0xD2
         (Solaris fasttrap syscalls).  As part of this, note where we are, so we
         can back up the guest to this point if the syscall needs to
         be restarted. */
      IRJumpKind jump_kind;
      switch (d32) {
      case 0x80:
         jump_kind = Ijk_Sys_int128;
         break;
      case 0x81:
         jump_kind = Ijk_Sys_int129;
         break;
      case 0x82:
         jump_kind = Ijk_Sys_int130;
         break;
      case 0x91:
         jump_kind = Ijk_Sys_int145;
         break;
      case 0xD2:
         jump_kind = Ijk_Sys_int210;
         break;
      default:
         /* none of the above */
         goto decode_failure;
      }

      stmt( IRStmt_Put( OFFB_IP_AT_SYSCALL,
                        mkU32(guest_EIP_curr_instr) ) );
      jmp_lit(&dres, jump_kind, (Addr32)fix_ip(guest_EIP_bbstart+delta));
      vassert(dres.whatNext == Dis_StopHere);
      DIP("int $0x%x\n", d32);
      break;

   /* ------------------------ Jcond, byte offset --------- */

   case 0xEB: /* Jb (jump, byte offset) REL */
      d32 = (((Addr32)guest_EIP_bbstart)+delta+1) + getSDisp8(delta); 
      d32 = fix_ip(d32);
      delta++;
      if (resteerOkFn( callback_opaque, (Addr32)d32) ) {
         dres.whatNext   = Dis_ResteerU;
         dres.continueAt = (Addr32)d32;
      } else {
         jmp_lit(&dres, Ijk_Boring, d32);
         vassert(dres.whatNext == Dis_StopHere);
      }
      DIP("jmp-8 0x%x\n", d32);
      break;

   case 0xEA: {/* jump far, 16/32 address ABS */
      UInt addr_offset = getUDisp(2, delta); delta += 2;
      UInt selector = getSDisp16(delta); delta += 2;
      IRTemp final_addr = newTemp(Ity_I32);
      IRTemp tmp_selector = newTemp(Ity_I32);
      IRTemp tmp_addr_offset = newTemp(Ity_I16);
      assign(tmp_selector, mkU32(selector));
      assign(tmp_addr_offset, mkU16(addr_offset));
      assign(final_addr, realAddr(mkexpr(tmp_selector), mkexpr(tmp_addr_offset)));

      jmp_treg(&dres, Ijk_Boring, final_addr);
      vassert(dres.whatNext == Dis_StopHere);
      break;
   }
   case 0xE9: /* Jv (jump, 16/32 offset) REL */
      d32 = (((Addr32)guest_EIP_bbstart)+delta+sz) + getSDisp(2,delta); 
      d32 = fix_ip(d32);
      delta += 2;
      if (resteerOkFn( callback_opaque, (Addr32)d32) ) {
         dres.whatNext   = Dis_ResteerU;
         dres.continueAt = (Addr32)d32;
      } else {
         jmp_lit(&dres, Ijk_Boring, d32);
         vassert(dres.whatNext == Dis_StopHere);
      }
      DIP("jmp 0x%x\n", d32);
      break;

   case 0x70:
   case 0x71:
   case 0x72: /* JBb/JNAEb (jump below) */
   case 0x73: /* JNBb/JAEb (jump not below) */
   case 0x74: /* JZb/JEb (jump zero) */
   case 0x75: /* JNZb/JNEb (jump not zero) */
   case 0x76: /* JBEb/JNAb (jump below or equal) */
   case 0x77: /* JNBEb/JAb (jump not below or equal) */
   case 0x78: /* JSb (jump negative) */
   case 0x79: /* JSb (jump not negative) */
   case 0x7A: /* JP (jump parity even) */
   case 0x7B: /* JNP/JPO (jump parity odd) */
   case 0x7C: /* JLb/JNGEb (jump less) */
   case 0x7D: /* JGEb/JNLb (jump greater or equal) */
   case 0x7E: /* JLEb/JNGb (jump less or equal) */
   case 0x7F: /* JGb/JNLEb (jump greater) */
    { Int    jmpDelta;
      const HChar* comment  = "";
      jmpDelta = (Int)getSDisp8(delta);
      vassert(-128 <= jmpDelta && jmpDelta < 128);
      d32 = (((Addr32)guest_EIP_bbstart)+delta+1) + jmpDelta;
      d32 = fix_ip(d32);
      delta++;
      if (resteerCisOk
          && vex_control.guest_chase_cond
          && (Addr32)d32 != (Addr32)guest_EIP_bbstart
          && jmpDelta < 0
          && resteerOkFn( callback_opaque, (Addr32)d32) ) {
         /* Speculation: assume this backward branch is taken.  So we
            need to emit a side-exit to the insn following this one,
            on the negation of the condition, and continue at the
            branch target address (d32).  If we wind up back at the
            first instruction of the trace, just stop; it's better to
            let the IR loop unroller handle that case. */
         stmt( IRStmt_Exit( 
                  mk_x86g_calculate_condition((X86Condcode)(1 ^ (opc - 0x70))),
                  Ijk_Boring,
                  IRConst_U32(guest_EIP_bbstart+delta),
                  OFFB_EIP ) );
         dres.whatNext   = Dis_ResteerC;
         dres.continueAt = (Addr32)d32;
         comment = "(assumed taken)";
      }
      else
      if (resteerCisOk
          && vex_control.guest_chase_cond
          && (Addr32)d32 != (Addr32)guest_EIP_bbstart
          && jmpDelta >= 0
          && resteerOkFn( callback_opaque, 
                          (Addr32)(guest_EIP_bbstart+delta)) ) {
         /* Speculation: assume this forward branch is not taken.  So
            we need to emit a side-exit to d32 (the dest) and continue
            disassembling at the insn immediately following this
            one. */
         stmt( IRStmt_Exit( 
                  mk_x86g_calculate_condition((X86Condcode)(opc - 0x70)),
                  Ijk_Boring,
                  IRConst_U32(d32),
                  OFFB_EIP ) );
         dres.whatNext   = Dis_ResteerC;
         dres.continueAt = guest_EIP_bbstart + delta;
         comment = "(assumed not taken)";
      }
      else {
         /* Conservative default translation - end the block at this
            point. */
         jcc_01( &dres, (X86Condcode)(opc - 0x70), 
                 (Addr32)(guest_EIP_bbstart+delta), d32);
         vassert(dres.whatNext == Dis_StopHere);
      }
      DIP("j%s-8 0x%x %s\n", name_X86Condcode(opc - 0x70), d32, comment);
      break;
    }

   case 0xE3: /* JECXZ (for JCXZ see above) */
      d32 = (((Addr32)guest_EIP_bbstart)+delta+1) + getSDisp8(delta);
      d32 = fix_ip(d32);
      delta ++;
      stmt( IRStmt_Exit(
               binop(Iop_CmpEQ32, getIReg(4,R_ECX), mkU32(0)),
            Ijk_Boring,
            IRConst_U32(d32),
            OFFB_EIP
          ));
      if (vex_control.strict_block_end) {
         jmp_lit(&dres, Ijk_Boring, ((Addr32)guest_EIP_bbstart)+delta);
      }
      DIP("jecxz 0x%x\n", d32);
      break;

   case 0xE0: /* LOOPNE disp8: decrement count, jump if count != 0 && ZF==0 */
   case 0xE1: /* LOOPE  disp8: decrement count, jump if count != 0 && ZF==1 */
   case 0xE2: /* LOOP   disp8: decrement count, jump if count != 0 */
    { /* Again, the docs say this uses ECX/CX as a count depending on
         the address size override, not the operand one.  Since we
         don't handle address size overrides, I guess that means
         ECX. */
      IRExpr* zbit  = NULL;
      IRExpr* count = NULL;
      IRExpr* cond  = NULL;
      const HChar* xtra = NULL;

      d32 = (((Addr32)guest_EIP_bbstart)+delta+1) + getSDisp8(delta);
      d32 = fix_ip(d32);
      delta++;
      putIReg(4, R_ECX, binop(Iop_Sub32, getIReg(4,R_ECX), mkU32(1)));

      count = getIReg(4,R_ECX);
      cond = binop(Iop_CmpNE32, count, mkU32(0));
      switch (opc) {
         case 0xE2: 
            xtra = ""; 
            break;
         case 0xE1: 
            xtra = "e"; 
            zbit = mk_x86g_calculate_condition( X86CondZ );
	    cond = mkAnd1(cond, zbit);
            break;
         case 0xE0: 
            xtra = "ne";
            zbit = mk_x86g_calculate_condition( X86CondNZ );
	    cond = mkAnd1(cond, zbit);
            break;
         default:
	    vassert(0);
      }
      stmt( IRStmt_Exit(cond, Ijk_Boring, IRConst_U32(d32), OFFB_EIP) );

      if (vex_control.strict_block_end) {
         jmp_lit(&dres, Ijk_Boring, ((Addr32)guest_EIP_bbstart)+delta);
      }

      DIP("loop%s 0x%x\n", xtra, d32);
      break;
    }

   /* ------------------------ IMUL ----------------------- */

   case 0x69: /* IMUL Iv, Ev, Gv */
      delta = dis_imul_I_E_G ( sorb, 2, delta, 2 );
      break;
   case 0x6B: /* IMUL Ib, Ev, Gv */
      delta = dis_imul_I_E_G ( sorb, 2, delta, 1 );
      break;

   /* ------------------------ MOV ------------------------ */

   case 0x88: /* MOV Gb,Eb */
      delta = dis_mov_G_E(sorb, 1, delta);
      break;

   case 0x89: /* MOV Gv,Ev */
      delta = dis_mov_G_E(sorb, 2, delta);
      break;

   case 0x8A: /* MOV Eb,Gb */
      delta = dis_mov_E_G(sorb, 1, delta);
      break;
 
   case 0x8B: /* MOV Ev,Gv */
      delta = dis_mov_E_G(sorb, 2, delta);
      break;
 
   case 0x8D: /* LEA M,Gv */
      modrm = getIByte(delta);
      if (epartIsReg(modrm)) 
         goto decode_failure;
      /* NOTE!  this is the one place where a segment override prefix
         has no effect on the address calculation.  Therefore we pass
         zero instead of sorb here. */
      addr = disAMode ( &alen, &sorb, delta, dis_buf );
      sorb = UNDEFINED_SEG; /* no sorb for lea! */
      delta += alen;
      putIReg(2, gregOfRM(modrm), unop(Iop_32to16,mkexpr(addr)));
      DIP("lea%c %s, %s\n", nameISize(sz), dis_buf, 
                            nameIReg(sz,gregOfRM(modrm)));
      break;

   case 0x8C: /* MOV Sw,Ew -- MOV from a SEGMENT REGISTER */
      delta = dis_mov_Sw_Ew(sorb, sz, delta);
      break;

   case 0x8E: /* MOV Ew,Sw -- MOV to a SEGMENT REGISTER */
      delta = dis_mov_Ew_Sw(sorb, delta);
      break;
 
   case 0xA0: /* MOV Ob,AL */
      sz = 1;
      /* Fall through ... */
   case 0xA1: /* MOV Ov,eAX */
      d32 = getUDisp16(delta); delta += 2;
      ty = szToITy(sz);
      if (sorb == UNDEFINED_SEG){
         sorb = R_DS;
      }
      putIReg(sz, R_EAX, loadRealLE(ty, sorb, mkU16(d32)));
      DIP("mov%c %s0x%x, %s\n", nameISize(sz), sorbTxt(sorb),
                                d32, nameIReg(sz,R_EAX));
      break;

   case 0xA2: /* MOV Ob,AL */
      sz = 1;
      /* Fall through ... */
   case 0xA3: /* MOV eAX,Ov */
      d32 = getUDisp16(delta); delta += 2;
      ty = szToITy(sz);
      if (sorb == UNDEFINED_SEG){
         sorb = R_DS;
      }
      storeRealLE( mkexpr(addr),sorb , getIReg(sz,R_EAX) );
      DIP("mov%c %s, %s0x%x\n", nameISize(sz), nameIReg(sz,R_EAX),
                                sorbTxt(sorb), d32);
      break;

   case 0xB0: /* MOV imm,AL */
   case 0xB1: /* MOV imm,CL */
   case 0xB2: /* MOV imm,DL */
   case 0xB3: /* MOV imm,BL */
   case 0xB4: /* MOV imm,AH */
   case 0xB5: /* MOV imm,CH */
   case 0xB6: /* MOV imm,DH */
   case 0xB7: /* MOV imm,BH */
      d32 = getIByte(delta); delta += 1;
      putIReg(1, opc-0xB0, mkU8(d32));
      DIP("movb $0x%x,%s\n", d32, nameIReg(1,opc-0xB0));
      break;

   case 0xB8: /* MOV imm,eAX */
   case 0xB9: /* MOV imm,eCX */
   case 0xBA: /* MOV imm,eDX */
   case 0xBB: /* MOV imm,eBX */
   case 0xBC: /* MOV imm,eSP */
   case 0xBD: /* MOV imm,eBP */
   case 0xBE: /* MOV imm,eSI */
   case 0xBF: /* MOV imm,eDI */
      d32 = getUDisp(sz,delta); delta += sz;
      putIReg(sz, opc-0xB8, mkU(szToITy(sz), d32));
      DIP("mov%c $0x%x,%s\n", nameISize(sz), d32, nameIReg(sz,opc-0xB8));
      break;

   case 0xC6: /* C6 /0 = MOV Ib,Eb */
      sz = 1;
      /* fall through */
   case 0xC7: /* C7 /0 = MOV Iv,Ev */
      modrm = getIByte(delta);
      if (gregOfRM(modrm) == 0) {
         if (epartIsReg(modrm)) {
            delta++; /* mod/rm byte */
            d32 = getUDisp(sz,delta); delta += sz;
            putIReg(sz, eregOfRM(modrm), mkU(szToITy(sz), d32));
            DIP("mov%c $0x%x, %s\n", nameISize(sz), d32, 
                                     nameIReg(sz,eregOfRM(modrm)));
         } else {
            addr = disAMode ( &alen, &sorb, delta, dis_buf );
            delta += alen;
            d32 = getUDisp(sz,delta); delta += sz;
            storeRealLE(mkexpr(addr),sorb, mkU(szToITy(sz), d32));
            DIP("mov%c $0x%x, %s\n", nameISize(sz), d32, dis_buf);
         }
         break;
      }
      goto decode_failure;

   /* ------------------------ opl imm, A ----------------- */

   case 0x04: /* ADD Ib, AL */
      delta = dis_op_imm_A(  1, False, Iop_Add8, True, delta, "add" );
      break;
   case 0x05: /* ADD Iv, eAX */
      delta = dis_op_imm_A( sz, False, Iop_Add8, True, delta, "add" );
      break;

   case 0x0C: /* OR Ib, AL */
      delta = dis_op_imm_A(  1, False, Iop_Or8, True, delta, "or" );
      break;
   case 0x0D: /* OR Iv, eAX */
      delta = dis_op_imm_A( sz, False, Iop_Or8, True, delta, "or" );
      break;

   case 0x14: /* ADC Ib, AL */
      delta = dis_op_imm_A(  1, True, Iop_Add8, True, delta, "adc" );
      break;
   case 0x15: /* ADC Iv, eAX */
      delta = dis_op_imm_A( sz, True, Iop_Add8, True, delta, "adc" );
      break;

   case 0x1C: /* SBB Ib, AL */
      delta = dis_op_imm_A( 1, True, Iop_Sub8, True, delta, "sbb" );
      break;
   case 0x1D: /* SBB Iv, eAX */
      delta = dis_op_imm_A( sz, True, Iop_Sub8, True, delta, "sbb" );
      break;

   case 0x24: /* AND Ib, AL */
      delta = dis_op_imm_A(  1, False, Iop_And8, True, delta, "and" );
      break;
   case 0x25: /* AND Iv, eAX */
      delta = dis_op_imm_A( sz, False, Iop_And8, True, delta, "and" );
      break;

   case 0x2C: /* SUB Ib, AL */
      delta = dis_op_imm_A(  1, False, Iop_Sub8, True, delta, "sub" );
      break;
   case 0x2D: /* SUB Iv, eAX */
      delta = dis_op_imm_A( sz, False, Iop_Sub8, True, delta, "sub" );
      break;

   case 0x34: /* XOR Ib, AL */
      delta = dis_op_imm_A(  1, False, Iop_Xor8, True, delta, "xor" );
      break;
   case 0x35: /* XOR Iv, eAX */
      delta = dis_op_imm_A( sz, False, Iop_Xor8, True, delta, "xor" );
      break;

   case 0x3C: /* CMP Ib, AL */
      delta = dis_op_imm_A(  1, False, Iop_Sub8, False, delta, "cmp" );
      break;
   case 0x3D: /* CMP Iv, eAX */
      delta = dis_op_imm_A( sz, False, Iop_Sub8, False, delta, "cmp" );
      break;

   case 0xA8: /* TEST Ib, AL */
      delta = dis_op_imm_A(  1, False, Iop_And8, False, delta, "test" );
      break;
   case 0xA9: /* TEST Iv, eAX */
      delta = dis_op_imm_A( sz, False, Iop_And8, False, delta, "test" );
      break;

   /* ------------------------ opl Ev, Gv ----------------- */
 
   case 0x02: /* ADD Eb,Gb */
      delta = dis_op2_E_G ( sorb, False, Iop_Add8, True, 1, delta, "add" );
      break;
   case 0x03: /* ADD Ev,Gv */
      delta = dis_op2_E_G ( sorb, False, Iop_Add8, True, sz, delta, "add" );
      break;

   case 0x0A: /* OR Eb,Gb */
      delta = dis_op2_E_G ( sorb, False, Iop_Or8, True, 1, delta, "or" );
      break;
   case 0x0B: /* OR Ev,Gv */
      delta = dis_op2_E_G ( sorb, False, Iop_Or8, True, sz, delta, "or" );
      break;

   case 0x12: /* ADC Eb,Gb */
      delta = dis_op2_E_G ( sorb, True, Iop_Add8, True, 1, delta, "adc" );
      break;
   case 0x13: /* ADC Ev,Gv */
      delta = dis_op2_E_G ( sorb, True, Iop_Add8, True, sz, delta, "adc" );
      break;

   case 0x1A: /* SBB Eb,Gb */
      delta = dis_op2_E_G ( sorb, True, Iop_Sub8, True, 1, delta, "sbb" );
      break;
   case 0x1B: /* SBB Ev,Gv */
      delta = dis_op2_E_G ( sorb, True, Iop_Sub8, True, sz, delta, "sbb" );
      break;

   case 0x22: /* AND Eb,Gb */
      delta = dis_op2_E_G ( sorb, False, Iop_And8, True, 1, delta, "and" );
      break;
   case 0x23: /* AND Ev,Gv */
      delta = dis_op2_E_G ( sorb, False, Iop_And8, True, sz, delta, "and" );
      break;

   case 0x2A: /* SUB Eb,Gb */
      delta = dis_op2_E_G ( sorb, False, Iop_Sub8, True, 1, delta, "sub" );
      break;
   case 0x2B: /* SUB Ev,Gv */
      delta = dis_op2_E_G ( sorb, False, Iop_Sub8, True, sz, delta, "sub" );
      break;

   case 0x32: /* XOR Eb,Gb */
      delta = dis_op2_E_G ( sorb, False, Iop_Xor8, True, 1, delta, "xor" );
      break;
   case 0x33: /* XOR Ev,Gv */
      delta = dis_op2_E_G ( sorb, False, Iop_Xor8, True, sz, delta, "xor" );
      break;

   case 0x3A: /* CMP Eb,Gb */
      delta = dis_op2_E_G ( sorb, False, Iop_Sub8, False, 1, delta, "cmp" );
      break;
   case 0x3B: /* CMP Ev,Gv */
      delta = dis_op2_E_G ( sorb, False, Iop_Sub8, False, sz, delta, "cmp" );
      break;

   case 0x84: /* TEST Eb,Gb */
      delta = dis_op2_E_G ( sorb, False, Iop_And8, False, 1, delta, "test" );
      break;
   case 0x85: /* TEST Ev,Gv */
      delta = dis_op2_E_G ( sorb, False, Iop_And8, False, sz, delta, "test" );
      break;

   /* ------------------------ opl Gv, Ev ----------------- */

   case 0x00: /* ADD Gb,Eb */
      delta = dis_op2_G_E ( sorb, pfx_lock, False,
                            Iop_Add8, True, 1, delta, "add" );
      break;
   case 0x01: /* ADD Gv,Ev */
      delta = dis_op2_G_E ( sorb, pfx_lock, False,
                            Iop_Add8, True, sz, delta, "add" );
      break;

   case 0x08: /* OR Gb,Eb */
      delta = dis_op2_G_E ( sorb, pfx_lock, False,
                            Iop_Or8, True, 1, delta, "or" );
      break;
   case 0x09: /* OR Gv,Ev */
      delta = dis_op2_G_E ( sorb, pfx_lock, False,
                            Iop_Or8, True, sz, delta, "or" );
      break;

   case 0x10: /* ADC Gb,Eb */
      delta = dis_op2_G_E ( sorb, pfx_lock, True,
                            Iop_Add8, True, 1, delta, "adc" );
      break;
   case 0x11: /* ADC Gv,Ev */
      delta = dis_op2_G_E ( sorb, pfx_lock, True,
                            Iop_Add8, True, sz, delta, "adc" );
      break;

   case 0x18: /* SBB Gb,Eb */
      delta = dis_op2_G_E ( sorb, pfx_lock, True,
                            Iop_Sub8, True, 1, delta, "sbb" );
      break;
   case 0x19: /* SBB Gv,Ev */
      delta = dis_op2_G_E ( sorb, pfx_lock, True,
                            Iop_Sub8, True, sz, delta, "sbb" );
      break;

   case 0x20: /* AND Gb,Eb */
      delta = dis_op2_G_E ( sorb, pfx_lock, False,
                            Iop_And8, True, 1, delta, "and" );
      break;
   case 0x21: /* AND Gv,Ev */
      delta = dis_op2_G_E ( sorb, pfx_lock, False,
                            Iop_And8, True, sz, delta, "and" );
      break;

   case 0x28: /* SUB Gb,Eb */
      delta = dis_op2_G_E ( sorb, pfx_lock, False,
                            Iop_Sub8, True, 1, delta, "sub" );
      break;
   case 0x29: /* SUB Gv,Ev */
      delta = dis_op2_G_E ( sorb, pfx_lock, False,
                            Iop_Sub8, True, sz, delta, "sub" );
      break;

   case 0x30: /* XOR Gb,Eb */
      delta = dis_op2_G_E ( sorb, pfx_lock, False,
                            Iop_Xor8, True, 1, delta, "xor" );
      break;
   case 0x31: /* XOR Gv,Ev */
      delta = dis_op2_G_E ( sorb, pfx_lock, False,
                            Iop_Xor8, True, sz, delta, "xor" );
      break;

   case 0x38: /* CMP Gb,Eb */
      delta = dis_op2_G_E ( sorb, pfx_lock, False,
                            Iop_Sub8, False, 1, delta, "cmp" );
      break;
   case 0x39: /* CMP Gv,Ev */
      delta = dis_op2_G_E ( sorb, pfx_lock, False,
                            Iop_Sub8, False, sz, delta, "cmp" );
      break;

   /* ------------------------ POP ------------------------ */

   case 0x58: /* POP eAX */
   case 0x59: /* POP eCX */
   case 0x5A: /* POP eDX */
   case 0x5B: /* POP eBX */
   case 0x5D: /* POP eBP */
   case 0x5E: /* POP eSI */
   case 0x5F: /* POP eDI */
   case 0x5C: /* POP eSP */
      vassert(sz == 2 || sz == 4);
      t1 = newTemp(szToITy(sz)); t2 = newTemp(Ity_I32);
      assign(t2, getIReg(4, R_ESP));
      assign(t1, loadRealLE(szToITy(sz),R_SS,mkexpr(t2)));
      putIReg(4, R_ESP, binop(Iop_Add32, mkexpr(t2), mkU32(sz)));
      putIReg(sz, opc-0x58, mkexpr(t1));
      DIP("pop%c %s\n", nameISize(sz), nameIReg(sz,opc-0x58));
      break;

   case 0x9D: /* POPF */
      vassert(sz == 2 || sz == 4);
      t1 = newTemp(Ity_I32); t2 = newTemp(Ity_I32);
      assign(t2, getIReg(4, R_ESP));
      assign(t1, widenUto32(loadRealLE(szToITy(sz), R_SS,mkexpr(t2))));
      putIReg(4, R_ESP, binop(Iop_Add32, mkexpr(t2), mkU32(sz)));

      /* Generate IR to set %EFLAGS{O,S,Z,A,C,P,D,ID,AC} from the
	 value in t1. */
      set_EFLAGS_from_value( t1, True/*emit_AC_emwarn*/,
                                 ((Addr32)guest_EIP_bbstart)+delta );

      DIP("popf%c\n", nameISize(sz));
      break;

   case 0x61: /* POPA */
      /* This is almost certainly wrong for sz==2.  So ... */
      if (sz != 4) goto decode_failure;

      /* t5 is the old %ESP value. */
      t5 = newTemp(Ity_I32);
      assign( t5, getIReg(4, R_ESP) );

      /* Reload all the registers, except %esp. */
      putIReg(4,R_EAX, loadRealLE(Ity_I32, R_SS, binop(Iop_Add32,mkexpr(t5),mkU32(14)) ));
      putIReg(4,R_ECX, loadRealLE(Ity_I32, R_SS, binop(Iop_Add32,mkexpr(t5),mkU32(12)) ));
      putIReg(4,R_EDX, loadRealLE(Ity_I32, R_SS, binop(Iop_Add32,mkexpr(t5),mkU32(10)) ));
      putIReg(4,R_EBX, loadRealLE(Ity_I32, R_SS, binop(Iop_Add32,mkexpr(t5),mkU32(8)) ));
      /* ignore saved %ESP */
      putIReg(4,R_EBP, loadRealLE(Ity_I32, R_SS, binop(Iop_Add32,mkexpr(t5),mkU32( 4)) ));
      putIReg(4,R_ESI, loadRealLE(Ity_I32, R_SS, binop(Iop_Add32,mkexpr(t5),mkU32( 2)) ));
      putIReg(4,R_EDI, loadRealLE(Ity_I32, R_SS, binop(Iop_Add32,mkexpr(t5),mkU32( 0)) ));

      /* and move %ESP back up */
      putIReg( 4, R_ESP, binop(Iop_Add32, mkexpr(t5), mkU32(8*2)) );

      DIP("popa%c\n", nameISize(sz));
      break;

   case 0x8F: /* POPL/POPW m32 */
     { Int    len;
       UChar  rm = getIByte(delta);

       /* make sure this instruction is correct POP */
       if (epartIsReg(rm) || gregOfRM(rm) != 0)
          goto decode_failure;
       /* and has correct size */
       if (sz != 4 && sz != 2)
          goto decode_failure;
       ty = szToITy(sz);

       t1 = newTemp(Ity_I32); /* stack address */
       t3 = newTemp(ty); /* data */
       /* set t1 to ESP: t1 = ESP */
       assign( t1, getIReg(4, R_ESP) );
       /* load M[ESP] to virtual register t3: t3 = M[t1] */
       assign( t3, loadRealLE(ty, R_SS, mkexpr(t1)));
       
       /* increase ESP; must be done before the STORE.  Intel manual says:
            If the ESP register is used as a base register for addressing
            a destination operand in memory, the POP instruction computes
            the effective address of the operand after it increments the
            ESP register.
       */
       putIReg(4, R_ESP, binop(Iop_Add32, mkexpr(t1), mkU32(sz)) );

       /* resolve MODR/M */
       addr = disAMode ( &len, &sorb, delta, dis_buf);
       storeRealLE( mkexpr(addr),sorb , mkexpr(t3) );

       DIP("pop%c %s\n", sz==2 ? 'w' : 'l', dis_buf);

       delta += len;
       break;
     }

   case 0x1F: /* POP %DS */
      dis_pop_segreg( R_DS, sz ); break;
   case 0x07: /* POP %ES */
      dis_pop_segreg( R_ES, sz ); break;
   case 0x17: /* POP %SS */
      dis_pop_segreg( R_SS, sz ); break;

   /* ------------------------ PUSH ----------------------- */

   case 0x50: /* PUSH eAX */
   case 0x51: /* PUSH eCX */
   case 0x52: /* PUSH eDX */
   case 0x53: /* PUSH eBX */
   case 0x55: /* PUSH eBP */
   case 0x56: /* PUSH eSI */
   case 0x57: /* PUSH eDI */
   case 0x54: /* PUSH eSP */
      /* This is the Right Way, in that the value to be pushed is
         established before %esp is changed, so that pushl %esp
         correctly pushes the old value. */
      vassert(sz == 2 || sz == 4);
      ty = sz==2 ? Ity_I16 : Ity_I32;
      t1 = newTemp(ty); t2 = newTemp(Ity_I32);
      assign(t1, getIReg(sz, opc-0x50));
      assign(t2, binop(Iop_Sub32, getIReg(4, R_ESP), mkU32(sz)));
      putIReg(4, R_ESP, mkexpr(t2) );
      storeRealLE(mkexpr(t2),R_SS,mkexpr(t1));
      DIP("push%c %s\n", nameISize(sz), nameIReg(sz,opc-0x50));
      break;


   case 0x68: /* PUSH Iv */
      d32 = getUDisp(sz,delta); delta += sz;
      goto do_push_I;
   case 0x6A: /* PUSH Ib, sign-extended to sz */
      d32 = getSDisp8(delta); delta += 1;
      goto do_push_I;
   do_push_I:
      ty = szToITy(sz);
      t1 = newTemp(Ity_I32); t2 = newTemp(ty);
      assign( t1, binop(Iop_Sub32,getIReg(4,R_ESP),mkU32(sz)) );
      putIReg(4, R_ESP, mkexpr(t1) );
      /* stop mkU16 asserting if d32 is a negative 16-bit number
         (bug #132813) */
      if (ty == Ity_I16)
         d32 &= 0xFFFF;
      storeRealLE( mkexpr(t1), R_SS,  mkU(ty,d32) );
      DIP("push%c $0x%x\n", nameISize(sz), d32);
      break;

   case 0x9C: /* PUSHF */ {
      vassert(sz == 2 || sz == 4);

      t1 = newTemp(Ity_I32);
      assign( t1, binop(Iop_Sub32,getIReg(4,R_ESP),mkU32(sz)) );
      putIReg(4, R_ESP, mkexpr(t1) );

      /* Calculate OSZACP, and patch in fixed fields as per
         Intel docs. 
         - bit 1 is always 1
         - bit 9 is Interrupt Enable (should always be 1 in user mode?)
      */
      t2 = newTemp(Ity_I32);
      assign( t2, binop(Iop_Or32, 
                        mk_x86g_calculate_eflags_all(), 
                        mkU32( (1<<1)|(1<<9) ) ));

      /* Patch in the D flag.  This can simply be a copy of bit 10 of
         baseBlock[OFFB_DFLAG]. */
      t3 = newTemp(Ity_I32);
      assign( t3, binop(Iop_Or32,
                        mkexpr(t2),
                        binop(Iop_And32,
                              IRExpr_Get(OFFB_DFLAG,Ity_I32),
                              mkU32(1<<10))) 
            );

      /* And patch in the ID flag. */
      t4 = newTemp(Ity_I32);
      assign( t4, binop(Iop_Or32,
                        mkexpr(t3),
                        binop(Iop_And32,
                              binop(Iop_Shl32, IRExpr_Get(OFFB_IDFLAG,Ity_I32), 
                                               mkU8(21)),
                              mkU32(1<<21)))
            );

      /* And patch in the AC flag. */
      t5 = newTemp(Ity_I32);
      assign( t5, binop(Iop_Or32,
                        mkexpr(t4),
                        binop(Iop_And32,
                              binop(Iop_Shl32, IRExpr_Get(OFFB_ACFLAG,Ity_I32), 
                                               mkU8(18)),
                              mkU32(1<<18)))
            );

      /* if sz==2, the stored value needs to be narrowed. */
      if (sz == 2)
        storeRealLE( mkexpr(t1),R_SS ,  unop(Iop_32to16,mkexpr(t5)) );

      DIP("pushf%c\n", nameISize(sz));
      break;
   }

   case 0x60: /* PUSHA */
      /* This is the Right Way, in that the value to be pushed is
         established before %esp is changed, so that pusha
         correctly pushes the old %esp value.  New value of %esp is
         pushed at start. */
      /* t0 is the %ESP value we're going to push. */
      t0 = newTemp(Ity_I32);
      assign( t0, getIReg(4, R_ESP) );

      /* t5 will be the new %ESP value. */
      t5 = newTemp(Ity_I32);
      assign( t5, binop(Iop_Sub32, mkexpr(t0), mkU32(8*2)) );

      /* Update guest state before prodding memory. */
      putIReg(4, R_ESP, mkexpr(t5));

      /* Dump all the registers. */
      storeRealLE( binop(Iop_Add32,mkexpr(t5),mkU32(14)), R_SS, getIReg(4,R_EAX) );
      storeRealLE( binop(Iop_Add32,mkexpr(t5),mkU32(12)), R_SS, getIReg(4,R_ECX) );
      storeRealLE( binop(Iop_Add32,mkexpr(t5),mkU32(10)), R_SS, getIReg(4,R_EDX) );
      storeRealLE( binop(Iop_Add32,mkexpr(t5),mkU32( 8)), R_SS, getIReg(4,R_EBX) );
      storeRealLE( binop(Iop_Add32,mkexpr(t5),mkU32( 6)), R_SS, mkexpr(t0) /*esp*/);
      storeRealLE( binop(Iop_Add32,mkexpr(t5),mkU32( 4)), R_SS, getIReg(4,R_EBP) );
      storeRealLE( binop(Iop_Add32,mkexpr(t5),mkU32( 2)), R_SS, getIReg(4,R_ESI) );
      storeRealLE( binop(Iop_Add32,mkexpr(t5),mkU32( 0)), R_SS, getIReg(4,R_EDI) );

      DIP("pusha%c\n", nameISize(sz));
      break;

   case 0x0E: /* PUSH %CS */
      dis_push_segreg( R_CS, sz ); break;
   case 0x1E: /* PUSH %DS */
      dis_push_segreg( R_DS, sz ); break;
   case 0x06: /* PUSH %ES */
      dis_push_segreg( R_ES, sz ); break;
   case 0x16: /* PUSH %SS */
      dis_push_segreg( R_SS, sz ); break;

   /* ------------------------ SCAS et al ----------------- */

   case 0xA4: /* MOVS, no REP prefix */
   case 0xA5: 
      if (sorb != UNDEFINED_SEG)
         goto decode_failure; /* else dis_string_op asserts */
      dis_string_op( dis_MOVS, ( opc == 0xA4 ? 1 : sz ), "movs", sorb );
      break;

  case 0xA6: /* CMPSb, no REP prefix */
  case 0xA7:
      if (sorb != UNDEFINED_SEG)
         goto decode_failure; /* else dis_string_op asserts */
      dis_string_op( dis_CMPS, ( opc == 0xA6 ? 1 : sz ), "cmps", sorb );
      break;

   case 0xAA: /* STOS, no REP prefix */
   case 0xAB:
      if (sorb != UNDEFINED_SEG)
         goto decode_failure; /* else dis_string_op asserts */
      dis_string_op( dis_STOS, ( opc == 0xAA ? 1 : sz ), "stos", sorb );
      break;

   case 0xAC: /* LODS, no REP prefix */
   case 0xAD:
      if (sorb != UNDEFINED_SEG)
         goto decode_failure; /* else dis_string_op asserts */
      dis_string_op( dis_LODS, ( opc == 0xAC ? 1 : sz ), "lods", sorb );
      break;

   case 0xAE: /* SCAS, no REP prefix */
   case 0xAF:
      if (sorb != UNDEFINED_SEG) 
         goto decode_failure; /* else dis_string_op asserts */
      dis_string_op( dis_SCAS, ( opc == 0xAE ? 1 : sz ), "scas", sorb );
      break;


   case 0xFC: /* CLD */
      stmt( IRStmt_Put( OFFB_DFLAG, mkU32(1)) );
      DIP("cld\n");
      break;

   case 0xFD: /* STD */
      stmt( IRStmt_Put( OFFB_DFLAG, mkU32(0xFFFFFFFF)) );
      DIP("std\n");
      break;

   case 0xF8: /* CLC */
   case 0xF9: /* STC */
   case 0xF5: /* CMC */
      t0 = newTemp(Ity_I32);
      t1 = newTemp(Ity_I32);
      assign( t0, mk_x86g_calculate_eflags_all() );
      switch (opc) {
         case 0xF8: 
            assign( t1, binop(Iop_And32, mkexpr(t0), 
                                         mkU32(~X86G_CC_MASK_C)));
            DIP("clc\n");
            break;
         case 0xF9: 
            assign( t1, binop(Iop_Or32, mkexpr(t0), 
                                        mkU32(X86G_CC_MASK_C)));
            DIP("stc\n");
            break;
         case 0xF5: 
            assign( t1, binop(Iop_Xor32, mkexpr(t0), 
                                         mkU32(X86G_CC_MASK_C)));
            DIP("cmc\n");
            break;
         default: 
            vpanic("disInstr(x86)(clc/stc/cmc)");
      }
      stmt( IRStmt_Put( OFFB_CC_OP,   mkU32(X86G_CC_OP_COPY) ));
      stmt( IRStmt_Put( OFFB_CC_DEP2, mkU32(0) ));
      stmt( IRStmt_Put( OFFB_CC_DEP1, mkexpr(t1) ));
      /* Set NDEP even though it isn't used.  This makes redundant-PUT
         elimination of previous stores to this field work better. */
      stmt( IRStmt_Put( OFFB_CC_NDEP, mkU32(0) ));
      break;

   case 0xD6: /* SALC */
      t0 = newTemp(Ity_I32);
      t1 = newTemp(Ity_I32);
      assign( t0,  binop(Iop_And32,
                         mk_x86g_calculate_eflags_c(),
                         mkU32(1)) );
      assign( t1, binop(Iop_Sar32, 
                        binop(Iop_Shl32, mkexpr(t0), mkU8(31)), 
                        mkU8(31)) );
      putIReg(1, R_EAX, unop(Iop_32to8, mkexpr(t1)) );
      DIP("salc\n");
      break;

   /* REPNE prefix insn */
   case 0xF2: { 
      Addr32 eip_orig = fix_ip(guest_EIP_bbstart + delta_start);
      if (sorb != UNDEFINED_SEG) goto decode_failure;
      abyte = getIByte(delta); delta++;
      Addr32 eip_next=fix_ip(guest_EIP_bbstart+delta);
      

      switch (abyte) {
      /* According to the Intel manual, "repne movs" should never occur, but
       * in practice it has happened, so allow for it here... */
      case 0xA4: sz = 1;   /* REPNE MOVS<sz> */
      case 0xA5: 
         dis_REP_op ( &dres, X86CondNZ, dis_MOVS, sz, eip_orig,
                             eip_next, "repne movs" );
         break;

      case 0xA6: sz = 1;   /* REPNE CMP<sz> */
      case 0xA7:
         dis_REP_op ( &dres, X86CondNZ, dis_CMPS, sz, eip_orig, 
                             eip_next, "repne cmps" );
         break;

      case 0xAA: sz = 1;   /* REPNE STOS<sz> */
      case 0xAB:
         dis_REP_op ( &dres, X86CondNZ, dis_STOS, sz, eip_orig, 
                             eip_next, "repne stos" );
         break;
      case 0xAC: sz = 1;   /* REPNE STOS<sz> */
      case 0xAD:
         dis_REP_op ( &dres, X86CondNZ, dis_STOS, sz, eip_orig, 
                             eip_next, "repne stos" );
         break;

      case 0xAE: sz = 1;   /* REPNE SCAS<sz> */
      case 0xAF:
         dis_REP_op ( &dres, X86CondNZ, dis_SCAS, sz, eip_orig,
                             eip_next, "repne scas" );
         break;

      default:
         goto decode_failure;
      }
      break;
   }

   /* REP/REPE prefix insn (for SCAS and CMPS, 0xF3 means REPE,
      for the rest, it means REP) */
   case 0xF3: { 
      Addr32 eip_orig = fix_ip(guest_EIP_bbstart + delta_start);
      abyte = getIByte(delta); delta++;
      Addr32 eip_next=fix_ip(guest_EIP_bbstart+delta);

      if (sorb != UNDEFINED_SEG) goto decode_failure;

      switch (abyte) {
      case 0xA4: sz = 1;   /* REP MOVS<sz> */
      case 0xA5:
         dis_REP_op ( &dres, X86CondAlways, dis_MOVS, sz, eip_orig, 
                             guest_EIP_bbstart+delta, "rep movs" );
         break;

      case 0xA6: sz = 1;   /* REPE CMP<sz> */
      case 0xA7:
         dis_REP_op ( &dres, X86CondZ, dis_CMPS, sz, eip_orig, 
                             guest_EIP_bbstart+delta, "repe cmps" );
         break;

      case 0xAA: sz = 1;   /* REP STOS<sz> */
      case 0xAB:
         dis_REP_op ( &dres, X86CondAlways, dis_STOS, sz, eip_orig, 
                             guest_EIP_bbstart+delta, "rep stos" );
         break;

      case 0xAC: sz = 1;   /* REP LODS<sz> */
      case 0xAD:
         dis_REP_op ( &dres, X86CondAlways, dis_LODS, sz, eip_orig, 
                             guest_EIP_bbstart+delta, "rep lods" );
         break;

      case 0xAE: sz = 1;   /* REPE SCAS<sz> */
      case 0xAF: 
         dis_REP_op ( &dres, X86CondZ, dis_SCAS, sz, eip_orig, 
                             guest_EIP_bbstart+delta, "repe scas" );
         break;
      default:
         goto decode_failure;
      }
      break;
   }

   /* ------------------------ XCHG ----------------------- */

   /* XCHG reg,mem automatically asserts LOCK# even without a LOCK
      prefix; hence it must be translated with an IRCAS (at least, the
      memory variant). */
   case 0x86: /* XCHG Gb,Eb */
      sz = 1;
      /* Fall through ... */
   case 0x87: /* XCHG Gv,Ev */
      modrm = getIByte(delta);
      ty = szToITy(sz);
      t1 = newTemp(ty); t2 = newTemp(ty);
      if (epartIsReg(modrm)) {
         assign(t1, getIReg(sz, eregOfRM(modrm)));
         assign(t2, getIReg(sz, gregOfRM(modrm)));
         putIReg(sz, gregOfRM(modrm), mkexpr(t1));
         putIReg(sz, eregOfRM(modrm), mkexpr(t2));
         delta++;
         DIP("xchg%c %s, %s\n", 
             nameISize(sz), nameIReg(sz,gregOfRM(modrm)), 
                            nameIReg(sz,eregOfRM(modrm)));
      } else {
         *expect_CAS = True;
         addr = disAMode ( &alen, &sorb, delta, dis_buf );
         assign( t1, loadRealLE(ty,R_DS,mkexpr(addr)) );
         assign( t2, getIReg(sz,gregOfRM(modrm)) );
         casLE( mkexpr(addr),
                mkexpr(t1), mkexpr(t2), guest_EIP_curr_instr );
         putIReg( sz, gregOfRM(modrm), mkexpr(t1) );
         delta += alen;
         DIP("xchg%c %s, %s\n", nameISize(sz), 
                                nameIReg(sz,gregOfRM(modrm)), dis_buf);
      }
      break;

   case 0x90: /* XCHG eAX,eAX */
      DIP("nop\n");
      break;
   case 0x91: /* XCHG eAX,eCX */
   case 0x92: /* XCHG eAX,eDX */
   case 0x93: /* XCHG eAX,eBX */
   case 0x94: /* XCHG eAX,eSP */
   case 0x95: /* XCHG eAX,eBP */
   case 0x96: /* XCHG eAX,eSI */
   case 0x97: /* XCHG eAX,eDI */
      codegen_xchg_eAX_Reg ( sz, opc - 0x90 );
      break;

   /* ------------------------ XLAT ----------------------- */

   case 0xD7: /* XLAT */
      if(sorb == UNDEFINED_SEG){
         sorb = R_DS;
      }
      putIReg(1,R_EAX/*AL*/,loadRealLE(Ity_I8, sorb, binop(Iop_Add32, getIReg(4, R_EBX), unop(Iop_8Uto32, getIReg(1, R_EAX/*AL*/)))));

      DIP("xlat%c [ebx]\n", nameISize(sz));
      break;

   /* ------------------------ IN / OUT ----------------------- */

   case 0xE4: /* IN imm8, AL */
      sz = 1; 
      t1 = newTemp(Ity_I32);
      abyte = getIByte(delta); delta++;
      assign(t1, mkU32( abyte & 0xFF ));
      DIP("in%c $%d,%s\n", nameISize(sz), abyte, nameIReg(sz,R_EAX));
      goto do_IN;
   case 0xE5: /* IN imm8, eAX */
      vassert(sz == 2 || sz == 4);
      t1 = newTemp(Ity_I32);
      abyte = getIByte(delta); delta++;
      assign(t1, mkU32( abyte & 0xFF ));
      DIP("in%c $%d,%s\n", nameISize(sz), abyte, nameIReg(sz,R_EAX));
      goto do_IN;
   case 0xEC: /* IN %DX, AL */
      sz = 1; 
      t1 = newTemp(Ity_I32);
      assign(t1, unop(Iop_16Uto32, getIReg(2, R_EDX)));
      DIP("in%c %s,%s\n", nameISize(sz), nameIReg(2,R_EDX), 
                                         nameIReg(sz,R_EAX));
      goto do_IN;
   case 0xED: /* IN %DX, eAX */
      vassert(sz == 2 || sz == 4);
      t1 = newTemp(Ity_I32);
      assign(t1, unop(Iop_16Uto32, getIReg(2, R_EDX)));
      DIP("in%c %s,%s\n", nameISize(sz), nameIReg(2,R_EDX), 
                                         nameIReg(sz,R_EAX));
      goto do_IN;
   do_IN: {
      /* At this point, sz indicates the width, and t1 is a 32-bit
         value giving port number. */
      IRDirty* d;
      vassert(sz == 1 || sz == 2 || sz == 4);
      ty = szToITy(sz);
      t2 = newTemp(Ity_I32);
      d = unsafeIRDirty_1_N( 
             t2,
             0/*regparms*/, 
             "x86g_dirtyhelper_IN", 
             &x86g_dirtyhelper_IN,
             mkIRExprVec_2( mkexpr(t1), mkU32(sz) )
          );
      /* do the call, dumping the result in t2. */
      stmt( IRStmt_Dirty(d) );
      putIReg(sz, R_EAX, narrowTo( ty, mkexpr(t2) ) );
      break;
   }

   case 0xE6: /* OUT AL, imm8 */
      sz = 1;
      t1 = newTemp(Ity_I32);
      abyte = getIByte(delta); delta++;
      assign( t1, mkU32( abyte & 0xFF ) );
      DIP("out%c %s,$%d\n", nameISize(sz), nameIReg(sz,R_EAX), abyte);
      goto do_OUT;
   case 0xE7: /* OUT eAX, imm8 */
      vassert(sz == 2 || sz == 4);
      t1 = newTemp(Ity_I32);
      abyte = getIByte(delta); delta++;
      assign( t1, mkU32( abyte & 0xFF ) );
      DIP("out%c %s,$%d\n", nameISize(sz), nameIReg(sz,R_EAX), abyte);
      goto do_OUT;
   case 0xEE: /* OUT AL, %DX */
      sz = 1;
      t1 = newTemp(Ity_I32);
      assign( t1, unop(Iop_16Uto32, getIReg(2, R_EDX)) );
      DIP("out%c %s,%s\n", nameISize(sz), nameIReg(sz,R_EAX),
                                          nameIReg(2,R_EDX));
      goto do_OUT;
   case 0xEF: /* OUT eAX, %DX */
      vassert(sz == 2 || sz == 4);
      t1 = newTemp(Ity_I32);
      assign( t1, unop(Iop_16Uto32, getIReg(2, R_EDX)) );
      DIP("out%c %s,%s\n", nameISize(sz), nameIReg(sz,R_EAX),
                                          nameIReg(2,R_EDX));
      goto do_OUT;
   do_OUT: {
      /* At this point, sz indicates the width, and t1 is a 32-bit
         value giving port number. */
      IRDirty* d;
      vassert(sz == 1 || sz == 2 || sz == 4);
      ty = szToITy(sz);
      d = unsafeIRDirty_0_N( 
             0/*regparms*/, 
             "x86g_dirtyhelper_OUT", 
             &x86g_dirtyhelper_OUT,
             mkIRExprVec_3( mkexpr(t1),
                            widenUto32( getIReg(sz, R_EAX) ), 
                            mkU32(sz) )
          );
      stmt( IRStmt_Dirty(d) );
      break;
   }

   /* ------------------------ (Grp1 extensions) ---------- */

   case 0x82: /* Grp1 Ib,Eb too.  Apparently this is the same as 
                 case 0x80, but only in 32-bit mode. */
      /* fallthru */
   case 0x80: /* Grp1 Ib,Eb */
      modrm = getIByte(delta);
      am_sz = lengthAMode(delta);
      sz    = 1;
      d_sz  = 1;
      d32   = getUChar(delta + am_sz);
      delta = dis_Grp1 ( sorb, pfx_lock, delta, modrm, am_sz, d_sz, sz, d32 );
      break;

   case 0x81: /* Grp1 Iv,Ev */
      modrm = getIByte(delta);
      am_sz = lengthAMode(delta);
      d_sz  = sz;
      d32   = getUDisp(d_sz, delta + am_sz);
      delta = dis_Grp1 ( sorb, pfx_lock, delta, modrm, am_sz, d_sz, sz, d32 );
      break;

   case 0x83: /* Grp1 Ib,Ev */
      modrm = getIByte(delta);
      am_sz = lengthAMode(delta);
      d_sz  = 1;
      d32   = getSDisp8(delta + am_sz);
      delta = dis_Grp1 ( sorb, pfx_lock, delta, modrm, am_sz, d_sz, sz, d32 );
      break;

   /* ------------------------ (Grp2 extensions) ---------- */

   case 0xC0: { /* Grp2 Ib,Eb */
      Bool decode_OK = True;
      modrm = getIByte(delta);
      am_sz = lengthAMode(delta);
      d_sz  = 1;
      d32   = getUChar(delta + am_sz);
      sz    = 1;
      delta = dis_Grp2 ( sorb, delta, modrm, am_sz, d_sz, sz, 
                         mkU8(d32 & 0xFF), NULL, &decode_OK );
      if (!decode_OK)
         goto decode_failure;
      break;
   }
   case 0xC1: { /* Grp2 Ib,Ev */
      Bool decode_OK = True;
      modrm = getIByte(delta);
      am_sz = lengthAMode(delta);
      d_sz  = 1;
      d32   = getUChar(delta + am_sz);
      delta = dis_Grp2 ( sorb, delta, modrm, am_sz, d_sz, sz, 
                         mkU8(d32 & 0xFF), NULL, &decode_OK );
      if (!decode_OK)
         goto decode_failure;
      break;
   }
   case 0xD0: { /* Grp2 1,Eb */
      Bool decode_OK = True;
      modrm = getIByte(delta);
      am_sz = lengthAMode(delta);
      d_sz  = 0;
      d32   = 1;
      sz    = 1;
      delta = dis_Grp2 ( sorb, delta, modrm, am_sz, d_sz, sz, 
                         mkU8(d32), NULL, &decode_OK );
      if (!decode_OK)
         goto decode_failure;
      break;
   }
   case 0xD1: { /* Grp2 1,Ev */
      Bool decode_OK = True;
      modrm = getUChar(delta);
      am_sz = lengthAMode(delta);
      d_sz  = 0;
      d32   = 1;
      delta = dis_Grp2 ( sorb, delta, modrm, am_sz, d_sz, sz, 
                         mkU8(d32), NULL, &decode_OK );
      if (!decode_OK)
         goto decode_failure;
      break;
   }
   case 0xD2: { /* Grp2 CL,Eb */
      Bool decode_OK = True;
      modrm = getUChar(delta);
      am_sz = lengthAMode(delta);
      d_sz  = 0;
      sz    = 1;
      delta = dis_Grp2 ( sorb, delta, modrm, am_sz, d_sz, sz, 
                         getIReg(1,R_ECX), "%cl", &decode_OK );
      if (!decode_OK)
         goto decode_failure;
      break;
   }
   case 0xD3: { /* Grp2 CL,Ev */
      Bool decode_OK = True;
      modrm = getIByte(delta);
      am_sz = lengthAMode(delta);
      d_sz  = 0;
      delta = dis_Grp2 ( sorb, delta, modrm, am_sz, d_sz, sz, 
                         getIReg(1,R_ECX), "%cl", &decode_OK );
      if (!decode_OK)
         goto decode_failure;
      break;
   }

   /* ------------------------ (Grp3 extensions) ---------- */

   case 0xF6: { /* Grp3 Eb */
      Bool decode_OK = True;
      delta = dis_Grp3 ( sorb, pfx_lock, 1, delta, &decode_OK );
      if (!decode_OK)
         goto decode_failure;
      break;
   }
   case 0xF7: { /* Grp3 Ev */
      Bool decode_OK = True;
      delta = dis_Grp3 ( sorb, pfx_lock, sz, delta, &decode_OK );
      if (!decode_OK)
         goto decode_failure;
      break;
   }

   /* ------------------------ (Grp4 extensions) ---------- */

   case 0xFE: { /* Grp4 Eb */
      Bool decode_OK = True;
      delta = dis_Grp4 ( sorb, pfx_lock, delta, &decode_OK );
      if (!decode_OK)
         goto decode_failure;
      break;
   }

   /* ------------------------ (Grp5 extensions) ---------- */

   case 0xFF: { /* Grp5 Ev */
      Bool decode_OK = True;
      delta = dis_Grp5 ( sorb, pfx_lock, sz, delta, &dres, &decode_OK );
      if (!decode_OK)
         goto decode_failure;
      break;
   }

   /* -------------------------- CLI/STI ------------------- */
   /* We treat them as NOP */
   case 0xFA: { /* CLI */
      break;
   }
   case 0xFB: { /* STI */
      break;
   }

   /* -------------------------- halt ---------------------- */
   case 0xF4: { /* hlt */
      jmp_lit(&dres, Ijk_SigTRAP, ((Addr32)guest_EIP_bbstart)+delta);
      vassert(dres.whatNext == Dis_StopHere);
      DIP("hlt\n");
      break;
   }

   /* ------------------------ Escapes to 2-byte opcodes -- */

   case 0x0F: {
      opc = getIByte(delta); delta++;
      switch (opc) {

      case 0x20: { /* mov r32, crX (X \in \{0, 2, 3, 4}) */
        UChar rm = getIByte(delta++);
        /* We only support cr0 for the moment */
        if (gregOfRM(rm) != 0)
          goto decode_failure;
        putIReg(4, gregOfRM(rm), mkU32(archinfo->x86_cr0));
        break;
      }
      case 0x22: {/* mov crX (X \in \{0, 2, 3, 4}), r32 */
        UChar rm = getIByte(delta++);
        /* We only support cr0 for the moment */
        if (gregOfRM(rm) != 0)
          goto decode_failure;
        IRTemp value = newTemp(Ity_I32);
        assign(value, getIReg(4, eregOfRM(rm)));
        IRDirty* d = unsafeIRDirty_0_N (
                           0/*regparms*/,
                           "x86g_dirtyhelper_write_cr0",
                           &x86g_dirtyhelper_write_cr0,
                           mkIRExprVec_1( mkexpr(value) )
                        );
        stmt( IRStmt_Dirty(d) );
        dres.whatNext    = Dis_StopHere;
        dres.jk_StopHere = Ijk_Yield;
        stmt( IRStmt_Put( OFFB_EIP, mkU32(guest_EIP_bbstart + delta) ) );
        break;
      }

      case 0x09: /* WBINVD */
        /* We treat it as NOP */
        break;

      /* =-=-=-=-=-=-=-=-=- Grp8 =-=-=-=-=-=-=-=-=-=-=-= */

      case 0xBA: { /* Grp8 Ib,Ev */
         Bool decode_OK = False;
         modrm = getUChar(delta);
         am_sz = lengthAMode(delta);
         d32   = getSDisp8(delta + am_sz);
         delta = dis_Grp8_Imm ( sorb, pfx_lock, delta, modrm, 
                                am_sz, sz, d32, &decode_OK );
         if (!decode_OK)
            goto decode_failure;
         break;
      }

      /* =-=-=-=-=-=-=-=-=- MOVZX, MOVSX =-=-=-=-=-=-=-= */

      case 0xB6: /* MOVZXb Eb,Gv */
         if (sz != 2 && sz != 4)
            goto decode_failure;
         delta = dis_movx_E_G ( sorb, delta, 1, sz, False );
         break;

      case 0xB7: /* MOVZXw Ew,Gv */
         if (sz != 4)
            goto decode_failure;
         delta = dis_movx_E_G ( sorb, delta, 2, 4, False );
         break;

      case 0xBE: /* MOVSXb Eb,Gv */
         if (sz != 2 && sz != 4)
            goto decode_failure;
         delta = dis_movx_E_G ( sorb, delta, 1, sz, True );
         break;

      case 0xBF: /* MOVSXw Ew,Gv */
         if (sz != 4 && /* accept movsww, sigh, see #250799 */sz != 2)
            goto decode_failure;
         delta = dis_movx_E_G ( sorb, delta, 2, sz, True );
         break;

      /* =-=-=-=-=-=-=-=-=- MUL/IMUL =-=-=-=-=-=-=-=-=-= */

      case 0xAF: /* IMUL Ev, Gv */
         delta = dis_mul_E_G ( sorb, sz, delta );
         break;

      /* =-=-=-=-=-=-=-=-=- NOPs =-=-=-=-=-=-=-=-=-=-=-= */

      case 0x1F:
         modrm = getUChar(delta);
         if (epartIsReg(modrm)) goto decode_failure;
         addr = disAMode ( &alen, &sorb, delta, dis_buf );
         delta += alen;
         DIP("nop%c %s\n", nameISize(sz), dis_buf);
         break;

      /* =-=-=-=-=-=-=-=-=- Jcond d32 -=-=-=-=-=-=-=-=-= */
      case 0x80:
      case 0x81:
      case 0x82: /* JBb/JNAEb (jump below) */
      case 0x83: /* JNBb/JAEb (jump not below) */
      case 0x84: /* JZb/JEb (jump zero) */
      case 0x85: /* JNZb/JNEb (jump not zero) */
      case 0x86: /* JBEb/JNAb (jump below or equal) */
      case 0x87: /* JNBEb/JAb (jump not below or equal) */
      case 0x88: /* JSb (jump negative) */
      case 0x89: /* JSb (jump not negative) */
      case 0x8A: /* JP (jump parity even) */
      case 0x8B: /* JNP/JPO (jump parity odd) */
      case 0x8C: /* JLb/JNGEb (jump less) */
      case 0x8D: /* JGEb/JNLb (jump greater or equal) */
      case 0x8E: /* JLEb/JNGb (jump less or equal) */
      case 0x8F: /* JGb/JNLEb (jump greater) */
       { Int    jmpDelta;
         const HChar* comment  = "";
         jmpDelta = (Int)getUDisp(2, delta);
         d32 = (((Addr32)guest_EIP_bbstart)+delta+2) + jmpDelta;
         delta += 2;
         if (resteerCisOk
             && vex_control.guest_chase_cond
             && (Addr32)d32 != (Addr32)guest_EIP_bbstart
             && jmpDelta < 0
             && resteerOkFn( callback_opaque, (Addr32)d32) ) {
            /* Speculation: assume this backward branch is taken.  So
               we need to emit a side-exit to the insn following this
               one, on the negation of the condition, and continue at
               the branch target address (d32).  If we wind up back at
               the first instruction of the trace, just stop; it's
               better to let the IR loop unroller handle that case.*/
            stmt( IRStmt_Exit( 
                     mk_x86g_calculate_condition((X86Condcode)
                                                 (1 ^ (opc - 0x80))),
                     Ijk_Boring,
                     IRConst_U32(guest_EIP_bbstart+delta),
                     OFFB_EIP ) );
            dres.whatNext   = Dis_ResteerC;
            dres.continueAt = (Addr32)d32;
            comment = "(assumed taken)";
         }
         else
         if (resteerCisOk
             && vex_control.guest_chase_cond
             && (Addr32)d32 != (Addr32)guest_EIP_bbstart
             && jmpDelta >= 0
             && resteerOkFn( callback_opaque, 
                             (Addr32)(guest_EIP_bbstart+delta)) ) {
            /* Speculation: assume this forward branch is not taken.
               So we need to emit a side-exit to d32 (the dest) and
               continue disassembling at the insn immediately
               following this one. */
            stmt( IRStmt_Exit( 
                     mk_x86g_calculate_condition((X86Condcode)(opc - 0x80)),
                     Ijk_Boring,
                     IRConst_U32(d32),
                     OFFB_EIP ) );
            dres.whatNext   = Dis_ResteerC;
            dres.continueAt = guest_EIP_bbstart + delta;
            comment = "(assumed not taken)";
         }
         else {
            /* Conservative default translation - end the block at
               this point. */
            jcc_01( &dres, (X86Condcode)(opc - 0x80), 
                    (Addr32)(guest_EIP_bbstart+delta), d32);
            vassert(dres.whatNext == Dis_StopHere);
         }
         DIP("j%s-32 0x%x %s\n", name_X86Condcode(opc - 0x80), d32, comment);
         break;
       }

      /* =-=-=-=-=-=-=-=-=- RDTSC -=-=-=-=-=-=-=-=-=-=-= */
      case 0x31: { /* RDTSC */
         IRTemp   val  = newTemp(Ity_I64);
         IRExpr** args = mkIRExprVec_0();
         IRDirty* d    = unsafeIRDirty_1_N ( 
                            val, 
                            0/*regparms*/, 
                            "x86g_dirtyhelper_RDTSC", 
                            &x86g_dirtyhelper_RDTSC, 
                            args 
                         );
         /* execute the dirty call, dumping the result in val. */
         stmt( IRStmt_Dirty(d) );
         putIReg(4, R_EDX, unop(Iop_64HIto32, mkexpr(val)));
         putIReg(4, R_EAX, unop(Iop_64to32, mkexpr(val)));
         DIP("rdtsc\n");
         break;
      }


      /* =-=-=-=-=-=-=-=-=- SETcc Eb =-=-=-=-=-=-=-=-=-= */
      case 0x90:
      case 0x91:
      case 0x92: /* set-Bb/set-NAEb (jump below) */
      case 0x93: /* set-NBb/set-AEb (jump not below) */
      case 0x94: /* set-Zb/set-Eb (jump zero) */
      case 0x95: /* set-NZb/set-NEb (jump not zero) */
      case 0x96: /* set-BEb/set-NAb (jump below or equal) */
      case 0x97: /* set-NBEb/set-Ab (jump not below or equal) */
      case 0x98: /* set-Sb (jump negative) */
      case 0x99: /* set-Sb (jump not negative) */
      case 0x9A: /* set-P (jump parity even) */
      case 0x9B: /* set-NP (jump parity odd) */
      case 0x9C: /* set-Lb/set-NGEb (jump less) */
      case 0x9D: /* set-GEb/set-NLb (jump greater or equal) */
      case 0x9E: /* set-LEb/set-NGb (jump less or equal) */
      case 0x9F: /* set-Gb/set-NLEb (jump greater) */
         t1 = newTemp(Ity_I8);
         assign( t1, unop(Iop_1Uto8,mk_x86g_calculate_condition(opc-0x90)) );
         modrm = getIByte(delta);
         if (epartIsReg(modrm)) {
            delta++;
            putIReg(1, eregOfRM(modrm), mkexpr(t1));
            DIP("set%s %s\n", name_X86Condcode(opc-0x90), 
                              nameIReg(1,eregOfRM(modrm)));
         } else {
           addr = disAMode ( &alen, &sorb, delta, dis_buf );
           delta += alen;
           storeRealLE( mkexpr(addr),sorb, mkexpr(t1) );
           DIP("set%s %s\n", name_X86Condcode(opc-0x90), dis_buf);
         }
         break;

      /* =-=-=-=-=-=-=-=-=- unimp2 =-=-=-=-=-=-=-=-=-=-= */

      default:
         goto decode_failure;
   } /* switch (opc) for the 2-byte opcodes */
   goto decode_success;
   } /* case 0x0F: of primary opcode */

   /* ------------------------ ??? ------------------------ */
  
  default:
  decode_failure:
   /* All decode failures end up here. */
   if (sigill_diag) {
      vex_printf("vex x86->IR: unhandled instruction bytes: "
                 "0x%x 0x%x 0x%x 0x%x\n",
                 getIByte(delta_start+0),
                 getIByte(delta_start+1),
                 getIByte(delta_start+2),
                 getIByte(delta_start+3));
   }

   /* Tell the dispatcher that this insn cannot be decoded, and so has
      not been executed, and (is currently) the next to be executed.
      EIP should be up-to-date since it made so at the start of each
      insn, but nevertheless be paranoid and update it again right
      now. */
   stmt( IRStmt_Put( OFFB_EIP, mkU32(guest_EIP_curr_instr) ) );
   jmp_lit(&dres, Ijk_NoDecode, guest_EIP_curr_instr);
   vassert(dres.whatNext == Dis_StopHere);
   dres.len = 0;
   /* We also need to say that a CAS is not expected now, regardless
      of what it might have been set to at the start of the function,
      since the IR that we've emitted just above (to synthesis a
      SIGILL) does not involve any CAS, and presumably no other IR has
      been emitted for this (non-decoded) insn. */
   *expect_CAS = False;
   return dres;

   } /* switch (opc) for the main (primary) opcode switch. */

  decode_success:
   /* All decode successes end up here. */
   switch (dres.whatNext) {
      case Dis_Continue:
         stmt( IRStmt_Put( OFFB_EIP, mkU32(guest_EIP_bbstart + delta) ) );
         break;
      case Dis_ResteerU:
      case Dis_ResteerC:
         stmt( IRStmt_Put( OFFB_EIP, mkU32(dres.continueAt) ) );
         break;
      case Dis_StopHere:
         break;
      default:
         vassert(0);
   }

   DIP("\n");
   dres.len = delta - delta_start;
   return dres;
}



/*------------------------------------------------------------*/
/*--- Top-level fn                                         ---*/
/*------------------------------------------------------------*/

/* Disassemble a single instruction into IR.  The instruction
   is located in host memory at &guest_code[delta]. */

DisResult disInstr_8086 ( IRSB*        irsb_IN,
                         Bool         (*resteerOkFn) ( void*, Addr ),
                         Bool         resteerCisOk,
                         void*        callback_opaque,
                         const UChar* guest_code_IN,
                         Long         delta,
                         Addr         guest_IP,
                         VexArch      guest_arch,
                         const VexArchInfo* archinfo,
                         const VexAbiInfo*  abiinfo,
                         VexEndness   host_endness_IN,
                         Bool         sigill_diag_IN )
{
   Int       i, x1, x2;
   Bool      expect_CAS, has_CAS;
   DisResult dres;
   /* Set globals (see top of this file) */
   vassert(guest_arch == VexArch8086);
   guest_code           = guest_code_IN;
   irsb                 = irsb_IN;
   host_endness         = host_endness_IN;
   guest_EIP_curr_instr = (Addr32)guest_IP;
   guest_EIP_bbstart    = (Addr32)toUInt(guest_IP - delta);

   x1 = irsb_IN->stmts_used;
   expect_CAS = False;
	
   ignore_seg_mode = archinfo->i8086_ignore_seg_mode;
   if((archinfo->i8086_cs_reg & UNINITALIZED_SREG == 0))
   {
      putSReg(R_CS, mkU16(archinfo->i8086_cs_reg & 0xffff));
   }
   if((archinfo->i8086_ds_reg & UNINITALIZED_SREG == 0))
   {
      putSReg(R_DS, mkU16(archinfo->i8086_ds_reg & 0xffff));
   }
   if((archinfo->i8086_es_reg & UNINITALIZED_SREG == 0))
   {
      putSReg(R_ES, mkU16(archinfo->i8086_es_reg & 0xffff));
   }
   if((archinfo->i8086_ss_reg & UNINITALIZED_SREG == 0))
   {
      putSReg(R_SS, mkU16(archinfo->i8086_ss_reg & 0xffff));
   }
	
   dres = disInstr_8086_WRK ( &expect_CAS, resteerOkFn,
                             resteerCisOk,
                             callback_opaque,
                             delta, archinfo, abiinfo, sigill_diag_IN );
   x2 = irsb_IN->stmts_used;
   vassert(x2 >= x1);

   /* See comment at the top of disInstr_X86_WRK for meaning of
      expect_CAS.  Here, we (sanity-)check for the presence/absence of
      IRCAS as directed by the returned expect_CAS value. */
   has_CAS = False;
   for (i = x1; i < x2; i++) {
      if (irsb_IN->stmts[i]->tag == Ist_CAS)
         has_CAS = True;
   }

   if (expect_CAS != has_CAS) {
      /* inconsistency detected.  re-disassemble the instruction so as
         to generate a useful error message; then assert. */
      vex_traceflags |= VEX_TRACE_FE;
      dres = disInstr_8086_WRK ( &expect_CAS, resteerOkFn,
                                resteerCisOk,
                                callback_opaque,
                                delta, archinfo, abiinfo, sigill_diag_IN );
      for (i = x1; i < x2; i++) {
         vex_printf("\t\t");
         ppIRStmt(irsb_IN->stmts[i]);
         vex_printf("\n");
      }
      /* Failure of this assertion is serious and denotes a bug in
         disInstr. */
      vpanic("disInstr_X86: inconsistency in LOCK prefix handling");
   }
   return dres;
}
#undef DIP
#undef DIS

/*--------------------------------------------------------------------*/
/*--- end                                         guest_8086_toIR.c ---*/
/*--------------------------------------------------------------------*/
