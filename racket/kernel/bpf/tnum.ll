; ModuleID = 'kernel/bpf/tnum.c'
source_filename = "kernel/bpf/tnum.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

module asm "\09.section \22__ksymtab_strings\22,\22aMS\22,%progbits,1\09"
module asm "__kstrtab_tnum_strn:\09\09\09\09\09"
module asm "\09.asciz \09\22tnum_strn\22\09\09\09\09\09"
module asm "__kstrtabns_tnum_strn:\09\09\09\09\09"
module asm "\09.asciz \09\22\22\09\09\09\09\09"
module asm "\09.previous\09\09\09\09\09\09"
module asm "\09.section \22___ksymtab_gpl+tnum_strn\22, \22a\22\09"
module asm "\09.balign\094\09\09\09\09\09"
module asm "__ksymtab_tnum_strn:\09\09\09\09"
module asm "\09.long\09tnum_strn- .\09\09\09\09"
module asm "\09.long\09__kstrtab_tnum_strn- .\09\09\09"
module asm "\09.long\09__kstrtabns_tnum_strn- .\09\09\09"
module asm "\09.previous\09\09\09\09\09"

%struct.tnum = type { i64, i64 }

@tnum_unknown = dso_local local_unnamed_addr constant %struct.tnum { i64 0, i64 -1 }, align 8, !dbg !0
@.str = private unnamed_addr constant [15 x i8] c"(%#llx; %#llx)\00", align 1
@__UNIQUE_ID___addressable_tnum_strn1 = internal global i8* bitcast (i32 (i8*, i64, i64, i64)* @tnum_strn to i8*), section ".discard.addressable", align 8, !dbg !29
@llvm.used = appending global [1 x i8*] [i8* bitcast (i8** @__UNIQUE_ID___addressable_tnum_strn1 to i8*)], section "llvm.metadata"

; Function Attrs: norecurse noredzone nounwind null_pointer_is_valid readnone sspstrong willreturn
define dso_local { i64, i64 } @tnum_const(i64 %0) local_unnamed_addr #0 !dbg !46 {
  call void @llvm.dbg.value(metadata i64 %0, metadata !50, metadata !DIExpression()), !dbg !51
  %2 = insertvalue { i64, i64 } undef, i64 %0, 0, !dbg !52
  %3 = insertvalue { i64, i64 } %2, i64 0, 1, !dbg !52
  ret { i64, i64 } %3, !dbg !52
}

; Function Attrs: noredzone nounwind null_pointer_is_valid readonly sspstrong
define dso_local { i64, i64 } @tnum_range(i64 %0, i64 %1) local_unnamed_addr #1 !dbg !53 {
  call void @llvm.dbg.value(metadata i64 %0, metadata !57, metadata !DIExpression()), !dbg !65
  call void @llvm.dbg.value(metadata i64 %1, metadata !58, metadata !DIExpression()), !dbg !65
  %3 = xor i64 %1, %0, !dbg !66
  call void @llvm.dbg.value(metadata i64 %3, metadata !59, metadata !DIExpression()), !dbg !65
  call void @llvm.dbg.value(metadata i64 %3, metadata !67, metadata !DIExpression()) #7, !dbg !74
  call void @llvm.dbg.value(metadata i32 -1, metadata !73, metadata !DIExpression()) #7, !dbg !74
  %4 = tail call i32 asm "bsrq $1,${0:q}", "=r,rm,0,~{dirflag},~{fpsr},~{flags}"(i64 %3, i32 -1) #8, !dbg !76, !srcloc !77
  call void @llvm.dbg.value(metadata i32 %4, metadata !73, metadata !DIExpression()) #7, !dbg !74
  %5 = add i32 %4, 1, !dbg !78
  %6 = and i32 %5, 255, !dbg !79
  call void @llvm.dbg.value(metadata i32 %5, metadata !61, metadata !DIExpression()), !dbg !65
  %7 = icmp ugt i32 %6, 63, !dbg !81
  %8 = zext i32 %6 to i64, !dbg !82
  %9 = shl nsw i64 -1, %8, !dbg !82
  %10 = xor i64 %9, -1, !dbg !82
  %11 = and i64 %9, %0, !dbg !82
  %12 = select i1 %7, i64 0, i64 %11, !dbg !82
  %13 = select i1 %7, i64 -1, i64 %10, !dbg !82
  %14 = insertvalue { i64, i64 } undef, i64 %12, 0, !dbg !83
  %15 = insertvalue { i64, i64 } %14, i64 %13, 1, !dbg !83
  ret { i64, i64 } %15, !dbg !83
}

; Function Attrs: norecurse noredzone nounwind null_pointer_is_valid readnone sspstrong willreturn
define dso_local { i64, i64 } @tnum_lshift(i64 %0, i64 %1, i8 zeroext %2) local_unnamed_addr #0 !dbg !84 {
  call void @llvm.dbg.value(metadata i64 %0, metadata !88, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !90
  call void @llvm.dbg.value(metadata i64 %1, metadata !88, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !90
  call void @llvm.dbg.value(metadata i8 %2, metadata !89, metadata !DIExpression()), !dbg !90
  %4 = zext i8 %2 to i64, !dbg !91
  %5 = shl i64 %0, %4, !dbg !91
  %6 = shl i64 %1, %4, !dbg !91
  %7 = insertvalue { i64, i64 } undef, i64 %5, 0, !dbg !92
  %8 = insertvalue { i64, i64 } %7, i64 %6, 1, !dbg !92
  ret { i64, i64 } %8, !dbg !92
}

; Function Attrs: norecurse noredzone nounwind null_pointer_is_valid readnone sspstrong willreturn
define dso_local { i64, i64 } @tnum_rshift(i64 %0, i64 %1, i8 zeroext %2) local_unnamed_addr #0 !dbg !93 {
  call void @llvm.dbg.value(metadata i64 %0, metadata !95, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !97
  call void @llvm.dbg.value(metadata i64 %1, metadata !95, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !97
  call void @llvm.dbg.value(metadata i8 %2, metadata !96, metadata !DIExpression()), !dbg !97
  %4 = zext i8 %2 to i64, !dbg !98
  %5 = lshr i64 %0, %4, !dbg !98
  %6 = lshr i64 %1, %4, !dbg !98
  %7 = insertvalue { i64, i64 } undef, i64 %5, 0, !dbg !99
  %8 = insertvalue { i64, i64 } %7, i64 %6, 1, !dbg !99
  ret { i64, i64 } %8, !dbg !99
}

; Function Attrs: norecurse noredzone nounwind null_pointer_is_valid readnone sspstrong willreturn
define dso_local { i64, i64 } @tnum_arshift(i64 %0, i64 %1, i8 zeroext %2, i8 zeroext %3) local_unnamed_addr #0 !dbg !100 {
  call void @llvm.dbg.value(metadata i64 %0, metadata !104, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !107
  call void @llvm.dbg.value(metadata i64 %1, metadata !104, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !107
  call void @llvm.dbg.value(metadata i8 %2, metadata !105, metadata !DIExpression()), !dbg !107
  call void @llvm.dbg.value(metadata i8 %3, metadata !106, metadata !DIExpression()), !dbg !107
  %5 = icmp eq i8 %3, 32, !dbg !108
  br i1 %5, label %6, label %14, !dbg !110

6:                                                ; preds = %4
  %7 = trunc i64 %0 to i32, !dbg !111
  %8 = zext i8 %2 to i32, !dbg !111
  %9 = ashr i32 %7, %8, !dbg !111
  %10 = zext i32 %9 to i64, !dbg !111
  %11 = trunc i64 %1 to i32, !dbg !111
  %12 = ashr i32 %11, %8, !dbg !111
  %13 = zext i32 %12 to i64, !dbg !111
  br label %18, !dbg !112

14:                                               ; preds = %4
  %15 = zext i8 %2 to i64, !dbg !113
  %16 = ashr i64 %0, %15, !dbg !113
  %17 = ashr i64 %1, %15, !dbg !113
  br label %18, !dbg !114

18:                                               ; preds = %14, %6
  %19 = phi i64 [ %10, %6 ], [ %16, %14 ], !dbg !115
  %20 = phi i64 [ %13, %6 ], [ %17, %14 ], !dbg !115
  %21 = insertvalue { i64, i64 } undef, i64 %19, 0, !dbg !116
  %22 = insertvalue { i64, i64 } %21, i64 %20, 1, !dbg !116
  ret { i64, i64 } %22, !dbg !116
}

; Function Attrs: norecurse noredzone nounwind null_pointer_is_valid readnone sspstrong willreturn
define dso_local { i64, i64 } @tnum_add(i64 %0, i64 %1, i64 %2, i64 %3) local_unnamed_addr #0 !dbg !117 {
  call void @llvm.dbg.value(metadata i64 %0, metadata !121, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !128
  call void @llvm.dbg.value(metadata i64 %1, metadata !121, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !128
  call void @llvm.dbg.value(metadata i64 %2, metadata !122, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !128
  call void @llvm.dbg.value(metadata i64 %3, metadata !122, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !128
  %5 = add i64 %3, %1, !dbg !129
  call void @llvm.dbg.value(metadata i64 %5, metadata !123, metadata !DIExpression()), !dbg !128
  %6 = add i64 %2, %0, !dbg !130
  call void @llvm.dbg.value(metadata i64 %6, metadata !124, metadata !DIExpression()), !dbg !128
  %7 = add i64 %5, %6, !dbg !131
  call void @llvm.dbg.value(metadata i64 %7, metadata !125, metadata !DIExpression()), !dbg !128
  %8 = xor i64 %7, %6, !dbg !132
  call void @llvm.dbg.value(metadata i64 %8, metadata !126, metadata !DIExpression()), !dbg !128
  %9 = or i64 %3, %1, !dbg !133
  %10 = or i64 %9, %8, !dbg !134
  call void @llvm.dbg.value(metadata i64 %10, metadata !127, metadata !DIExpression()), !dbg !128
  %11 = xor i64 %10, -1, !dbg !135
  %12 = and i64 %6, %11, !dbg !135
  %13 = insertvalue { i64, i64 } undef, i64 %12, 0, !dbg !136
  %14 = insertvalue { i64, i64 } %13, i64 %10, 1, !dbg !136
  ret { i64, i64 } %14, !dbg !136
}

; Function Attrs: norecurse noredzone nounwind null_pointer_is_valid readnone sspstrong willreturn
define dso_local { i64, i64 } @tnum_sub(i64 %0, i64 %1, i64 %2, i64 %3) local_unnamed_addr #0 !dbg !137 {
  call void @llvm.dbg.value(metadata i64 %0, metadata !139, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !146
  call void @llvm.dbg.value(metadata i64 %1, metadata !139, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !146
  call void @llvm.dbg.value(metadata i64 %2, metadata !140, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !146
  call void @llvm.dbg.value(metadata i64 %3, metadata !140, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !146
  %5 = sub i64 %0, %2, !dbg !147
  call void @llvm.dbg.value(metadata i64 %5, metadata !141, metadata !DIExpression()), !dbg !146
  %6 = add i64 %5, %1, !dbg !148
  call void @llvm.dbg.value(metadata i64 %6, metadata !142, metadata !DIExpression()), !dbg !146
  %7 = sub i64 %5, %3, !dbg !149
  call void @llvm.dbg.value(metadata i64 %7, metadata !143, metadata !DIExpression()), !dbg !146
  %8 = xor i64 %6, %7, !dbg !150
  call void @llvm.dbg.value(metadata i64 %8, metadata !144, metadata !DIExpression()), !dbg !146
  %9 = or i64 %3, %1, !dbg !151
  %10 = or i64 %9, %8, !dbg !152
  call void @llvm.dbg.value(metadata i64 %10, metadata !145, metadata !DIExpression()), !dbg !146
  %11 = xor i64 %10, -1, !dbg !153
  %12 = and i64 %5, %11, !dbg !153
  %13 = insertvalue { i64, i64 } undef, i64 %12, 0, !dbg !154
  %14 = insertvalue { i64, i64 } %13, i64 %10, 1, !dbg !154
  ret { i64, i64 } %14, !dbg !154
}

; Function Attrs: norecurse noredzone nounwind null_pointer_is_valid readnone sspstrong willreturn
define dso_local { i64, i64 } @tnum_and(i64 %0, i64 %1, i64 %2, i64 %3) local_unnamed_addr #0 !dbg !155 {
  call void @llvm.dbg.value(metadata i64 %0, metadata !157, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !162
  call void @llvm.dbg.value(metadata i64 %1, metadata !157, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !162
  call void @llvm.dbg.value(metadata i64 %2, metadata !158, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !162
  call void @llvm.dbg.value(metadata i64 %3, metadata !158, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !162
  %5 = or i64 %1, %0, !dbg !163
  call void @llvm.dbg.value(metadata i64 %5, metadata !159, metadata !DIExpression()), !dbg !162
  %6 = or i64 %3, %2, !dbg !164
  call void @llvm.dbg.value(metadata i64 %6, metadata !160, metadata !DIExpression()), !dbg !162
  %7 = and i64 %2, %0, !dbg !165
  call void @llvm.dbg.value(metadata i64 %7, metadata !161, metadata !DIExpression()), !dbg !162
  %8 = and i64 %6, %5, !dbg !166
  %9 = xor i64 %8, %7, !dbg !166
  %10 = insertvalue { i64, i64 } undef, i64 %7, 0, !dbg !167
  %11 = insertvalue { i64, i64 } %10, i64 %9, 1, !dbg !167
  ret { i64, i64 } %11, !dbg !167
}

; Function Attrs: norecurse noredzone nounwind null_pointer_is_valid readnone sspstrong willreturn
define dso_local { i64, i64 } @tnum_or(i64 %0, i64 %1, i64 %2, i64 %3) local_unnamed_addr #0 !dbg !168 {
  call void @llvm.dbg.value(metadata i64 %0, metadata !170, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !174
  call void @llvm.dbg.value(metadata i64 %1, metadata !170, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !174
  call void @llvm.dbg.value(metadata i64 %2, metadata !171, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !174
  call void @llvm.dbg.value(metadata i64 %3, metadata !171, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !174
  %5 = or i64 %2, %0, !dbg !175
  call void @llvm.dbg.value(metadata i64 %5, metadata !172, metadata !DIExpression()), !dbg !174
  %6 = or i64 %3, %1, !dbg !176
  call void @llvm.dbg.value(metadata i64 %6, metadata !173, metadata !DIExpression()), !dbg !174
  %7 = xor i64 %5, -1, !dbg !177
  %8 = and i64 %6, %7, !dbg !177
  %9 = insertvalue { i64, i64 } undef, i64 %5, 0, !dbg !178
  %10 = insertvalue { i64, i64 } %9, i64 %8, 1, !dbg !178
  ret { i64, i64 } %10, !dbg !178
}

; Function Attrs: norecurse noredzone nounwind null_pointer_is_valid readnone sspstrong willreturn
define dso_local { i64, i64 } @tnum_xor(i64 %0, i64 %1, i64 %2, i64 %3) local_unnamed_addr #0 !dbg !179 {
  call void @llvm.dbg.value(metadata i64 %0, metadata !181, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !185
  call void @llvm.dbg.value(metadata i64 %1, metadata !181, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !185
  call void @llvm.dbg.value(metadata i64 %2, metadata !182, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !185
  call void @llvm.dbg.value(metadata i64 %3, metadata !182, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !185
  %5 = xor i64 %2, %0, !dbg !186
  call void @llvm.dbg.value(metadata i64 %5, metadata !183, metadata !DIExpression()), !dbg !185
  %6 = or i64 %3, %1, !dbg !187
  call void @llvm.dbg.value(metadata i64 %6, metadata !184, metadata !DIExpression()), !dbg !185
  %7 = xor i64 %6, -1, !dbg !188
  %8 = and i64 %5, %7, !dbg !188
  %9 = insertvalue { i64, i64 } undef, i64 %8, 0, !dbg !189
  %10 = insertvalue { i64, i64 } %9, i64 %6, 1, !dbg !189
  ret { i64, i64 } %10, !dbg !189
}

; Function Attrs: norecurse noredzone nounwind null_pointer_is_valid readnone sspstrong
define dso_local { i64, i64 } @tnum_mul(i64 %0, i64 %1, i64 %2, i64 %3) local_unnamed_addr #2 !dbg !190 {
  call void @llvm.dbg.value(metadata i64 %0, metadata !192, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !196
  call void @llvm.dbg.value(metadata i64 %1, metadata !192, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !196
  call void @llvm.dbg.value(metadata i64 %2, metadata !193, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !196
  call void @llvm.dbg.value(metadata i64 %3, metadata !193, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !196
  call void @llvm.dbg.value(metadata i64 undef, metadata !194, metadata !DIExpression()), !dbg !196
  call void @llvm.dbg.value(metadata i64 0, metadata !195, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !196
  call void @llvm.dbg.value(metadata i64 0, metadata !195, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !196
  %5 = or i64 %1, %0, !dbg !197
  %6 = icmp eq i64 %5, 0, !dbg !197
  br i1 %6, label %35, label %7, !dbg !198

7:                                                ; preds = %4, %27
  %8 = phi i64 [ %30, %27 ], [ %1, %4 ]
  %9 = phi i64 [ %29, %27 ], [ %0, %4 ]
  %10 = phi i64 [ %32, %27 ], [ %3, %4 ]
  %11 = phi i64 [ %31, %27 ], [ %2, %4 ]
  %12 = phi i64 [ %28, %27 ], [ 0, %4 ]
  call void @llvm.dbg.value(metadata i64 %8, metadata !192, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !196
  call void @llvm.dbg.value(metadata i64 %9, metadata !192, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !196
  call void @llvm.dbg.value(metadata i64 %10, metadata !193, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !196
  call void @llvm.dbg.value(metadata i64 %11, metadata !193, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !196
  call void @llvm.dbg.value(metadata i64 0, metadata !195, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !196
  call void @llvm.dbg.value(metadata i64 %12, metadata !195, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !196
  %13 = and i64 %9, 1, !dbg !199
  %14 = icmp eq i64 %13, 0, !dbg !199
  br i1 %14, label %19, label %15, !dbg !202

15:                                               ; preds = %7
  call void @llvm.dbg.value(metadata i64 0, metadata !121, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !203
  call void @llvm.dbg.value(metadata i64 %12, metadata !121, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !203
  call void @llvm.dbg.value(metadata i64 0, metadata !122, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !203
  call void @llvm.dbg.value(metadata i64 %10, metadata !122, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !203
  call void @llvm.dbg.value(metadata i64 undef, metadata !123, metadata !DIExpression()), !dbg !203
  call void @llvm.dbg.value(metadata i64 0, metadata !124, metadata !DIExpression()), !dbg !203
  %16 = add i64 %12, %10, !dbg !205
  call void @llvm.dbg.value(metadata i64 %16, metadata !125, metadata !DIExpression()), !dbg !203
  call void @llvm.dbg.value(metadata i64 %16, metadata !126, metadata !DIExpression()), !dbg !203
  %17 = or i64 %10, %12, !dbg !206
  %18 = or i64 %17, %16, !dbg !207
  call void @llvm.dbg.value(metadata i64 %18, metadata !127, metadata !DIExpression()), !dbg !203
  call void @llvm.dbg.value(metadata i64 0, metadata !195, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !196
  call void @llvm.dbg.value(metadata i64 %18, metadata !195, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !196
  br label %27, !dbg !208

19:                                               ; preds = %7
  %20 = and i64 %8, 1, !dbg !209
  %21 = icmp eq i64 %20, 0, !dbg !209
  br i1 %21, label %27, label %22, !dbg !211

22:                                               ; preds = %19
  %23 = or i64 %10, %11, !dbg !212
  call void @llvm.dbg.value(metadata i64 0, metadata !121, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !213
  call void @llvm.dbg.value(metadata i64 %12, metadata !121, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !213
  call void @llvm.dbg.value(metadata i64 0, metadata !122, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !213
  call void @llvm.dbg.value(metadata i64 %23, metadata !122, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !213
  call void @llvm.dbg.value(metadata i64 undef, metadata !123, metadata !DIExpression()), !dbg !213
  call void @llvm.dbg.value(metadata i64 0, metadata !124, metadata !DIExpression()), !dbg !213
  %24 = add i64 %12, %23, !dbg !215
  call void @llvm.dbg.value(metadata i64 %24, metadata !125, metadata !DIExpression()), !dbg !213
  call void @llvm.dbg.value(metadata i64 %24, metadata !126, metadata !DIExpression()), !dbg !213
  %25 = or i64 %23, %12, !dbg !216
  %26 = or i64 %25, %24, !dbg !217
  call void @llvm.dbg.value(metadata i64 %26, metadata !127, metadata !DIExpression()), !dbg !213
  call void @llvm.dbg.value(metadata i64 0, metadata !195, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !196
  call void @llvm.dbg.value(metadata i64 %26, metadata !195, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !196
  br label %27, !dbg !218

27:                                               ; preds = %19, %22, %15
  %28 = phi i64 [ %18, %15 ], [ %26, %22 ], [ %12, %19 ], !dbg !196
  call void @llvm.dbg.value(metadata i64 0, metadata !195, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !196
  call void @llvm.dbg.value(metadata i64 %28, metadata !195, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !196
  call void @llvm.dbg.value(metadata i64 %9, metadata !95, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !219
  call void @llvm.dbg.value(metadata i64 %8, metadata !95, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !219
  call void @llvm.dbg.value(metadata i8 1, metadata !96, metadata !DIExpression()), !dbg !219
  %29 = lshr i64 %9, 1, !dbg !221
  %30 = lshr i64 %8, 1, !dbg !221
  call void @llvm.dbg.value(metadata i64 %29, metadata !192, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !196
  call void @llvm.dbg.value(metadata i64 %30, metadata !192, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !196
  call void @llvm.dbg.value(metadata i64 %11, metadata !88, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !222
  call void @llvm.dbg.value(metadata i64 %10, metadata !88, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !222
  call void @llvm.dbg.value(metadata i8 1, metadata !89, metadata !DIExpression()), !dbg !222
  %31 = shl i64 %11, 1, !dbg !224
  %32 = shl i64 %10, 1, !dbg !224
  call void @llvm.dbg.value(metadata i64 %29, metadata !192, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !196
  call void @llvm.dbg.value(metadata i64 %32, metadata !193, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !196
  call void @llvm.dbg.value(metadata i64 %31, metadata !193, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !196
  call void @llvm.dbg.value(metadata i64 0, metadata !195, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !196
  call void @llvm.dbg.value(metadata i64 %28, metadata !195, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !196
  %33 = or i64 %30, %29, !dbg !197
  %34 = icmp eq i64 %33, 0, !dbg !197
  br i1 %34, label %35, label %7, !dbg !198, !llvm.loop !225

35:                                               ; preds = %27, %4
  %36 = phi i64 [ 0, %4 ], [ %28, %27 ], !dbg !196
  %37 = mul i64 %2, %0, !dbg !227
  call void @llvm.dbg.value(metadata i64 %37, metadata !194, metadata !DIExpression()), !dbg !196
  call void @llvm.dbg.value(metadata i64 %37, metadata !121, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !228
  call void @llvm.dbg.value(metadata i64 0, metadata !121, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !228
  call void @llvm.dbg.value(metadata i64 0, metadata !122, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !228
  call void @llvm.dbg.value(metadata i64 %36, metadata !122, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !228
  call void @llvm.dbg.value(metadata i64 %36, metadata !123, metadata !DIExpression()), !dbg !228
  call void @llvm.dbg.value(metadata i64 %37, metadata !124, metadata !DIExpression()), !dbg !228
  %38 = add i64 %37, %36, !dbg !230
  call void @llvm.dbg.value(metadata i64 %38, metadata !125, metadata !DIExpression()), !dbg !228
  %39 = xor i64 %38, %37, !dbg !231
  call void @llvm.dbg.value(metadata i64 %39, metadata !126, metadata !DIExpression()), !dbg !228
  %40 = or i64 %39, %36, !dbg !232
  call void @llvm.dbg.value(metadata i64 %40, metadata !127, metadata !DIExpression()), !dbg !228
  %41 = xor i64 %40, -1, !dbg !233
  %42 = and i64 %37, %41, !dbg !233
  %43 = insertvalue { i64, i64 } undef, i64 %42, 0, !dbg !234
  %44 = insertvalue { i64, i64 } %43, i64 %40, 1, !dbg !234
  ret { i64, i64 } %44, !dbg !235
}

; Function Attrs: norecurse noredzone nounwind null_pointer_is_valid readnone sspstrong willreturn
define dso_local { i64, i64 } @tnum_intersect(i64 %0, i64 %1, i64 %2, i64 %3) local_unnamed_addr #0 !dbg !236 {
  call void @llvm.dbg.value(metadata i64 %0, metadata !238, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !242
  call void @llvm.dbg.value(metadata i64 %1, metadata !238, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !242
  call void @llvm.dbg.value(metadata i64 %2, metadata !239, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !242
  call void @llvm.dbg.value(metadata i64 %3, metadata !239, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !242
  %5 = or i64 %2, %0, !dbg !243
  call void @llvm.dbg.value(metadata i64 %5, metadata !240, metadata !DIExpression()), !dbg !242
  %6 = and i64 %3, %1, !dbg !244
  call void @llvm.dbg.value(metadata i64 %6, metadata !241, metadata !DIExpression()), !dbg !242
  %7 = xor i64 %6, -1, !dbg !245
  %8 = and i64 %5, %7, !dbg !245
  %9 = insertvalue { i64, i64 } undef, i64 %8, 0, !dbg !246
  %10 = insertvalue { i64, i64 } %9, i64 %6, 1, !dbg !246
  ret { i64, i64 } %10, !dbg !246
}

; Function Attrs: norecurse noredzone nounwind null_pointer_is_valid readnone sspstrong willreturn
define dso_local { i64, i64 } @tnum_union(i64 %0, i64 %1, i64 %2, i64 %3) local_unnamed_addr #0 !dbg !247 {
  call void @llvm.dbg.value(metadata i64 %0, metadata !249, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !253
  call void @llvm.dbg.value(metadata i64 %1, metadata !249, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !253
  call void @llvm.dbg.value(metadata i64 %2, metadata !250, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !253
  call void @llvm.dbg.value(metadata i64 %3, metadata !250, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !253
  %5 = or i64 %2, %0, !dbg !254
  call void @llvm.dbg.value(metadata i64 %5, metadata !251, metadata !DIExpression()), !dbg !253
  %6 = or i64 %3, %1, !dbg !255
  %7 = xor i64 %2, %0, !dbg !256
  %8 = or i64 %6, %7, !dbg !257
  call void @llvm.dbg.value(metadata i64 %8, metadata !252, metadata !DIExpression()), !dbg !253
  %9 = xor i64 %8, -1, !dbg !258
  %10 = and i64 %5, %9, !dbg !258
  %11 = insertvalue { i64, i64 } undef, i64 %10, 0, !dbg !259
  %12 = insertvalue { i64, i64 } %11, i64 %8, 1, !dbg !259
  ret { i64, i64 } %12, !dbg !259
}

; Function Attrs: norecurse noredzone nounwind null_pointer_is_valid readnone sspstrong
define dso_local { i64, i64 } @tnum_shl(i64 %0, i64 %1, i64 %2, i64 %3, i8 zeroext %4) local_unnamed_addr #2 !dbg !260 {
  call void @llvm.dbg.value(metadata i64 %0, metadata !264, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !268
  call void @llvm.dbg.value(metadata i64 %1, metadata !264, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !268
  call void @llvm.dbg.value(metadata i64 %2, metadata !265, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !268
  call void @llvm.dbg.value(metadata i64 %3, metadata !265, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !268
  call void @llvm.dbg.value(metadata i8 %4, metadata !266, metadata !DIExpression()), !dbg !268
  call void @llvm.dbg.value(metadata i8 1, metadata !267, metadata !DIExpression()), !dbg !268
  %6 = zext i8 %4 to i64, !dbg !269
  %7 = add nsw i64 %6, -1, !dbg !270
  call void @llvm.dbg.value(metadata i64 %2, metadata !157, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !271
  call void @llvm.dbg.value(metadata i64 %3, metadata !157, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !271
  call void @llvm.dbg.value(metadata i64 %7, metadata !158, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !271
  call void @llvm.dbg.value(metadata i64 0, metadata !158, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !271
  %8 = or i64 %3, %2, !dbg !273
  call void @llvm.dbg.value(metadata i64 %8, metadata !159, metadata !DIExpression()), !dbg !271
  call void @llvm.dbg.value(metadata i64 %7, metadata !160, metadata !DIExpression()), !dbg !271
  %9 = and i64 %7, %2, !dbg !274
  call void @llvm.dbg.value(metadata i64 %9, metadata !161, metadata !DIExpression()), !dbg !271
  %10 = and i64 %7, %8, !dbg !275
  call void @llvm.dbg.value(metadata i64 undef, metadata !265, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !268
  call void @llvm.dbg.value(metadata i64 undef, metadata !265, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !268
  call void @llvm.dbg.value(metadata i64 %1, metadata !264, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !268
  call void @llvm.dbg.value(metadata i64 %0, metadata !264, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !268
  call void @llvm.dbg.value(metadata i64 undef, metadata !265, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !268
  call void @llvm.dbg.value(metadata i64 %9, metadata !265, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !268
  call void @llvm.dbg.value(metadata i8 1, metadata !267, metadata !DIExpression()), !dbg !268
  %11 = icmp eq i64 %10, 0, !dbg !276
  br i1 %11, label %45, label %12, !dbg !277

12:                                               ; preds = %5
  %13 = xor i64 %10, %9, !dbg !275
  call void @llvm.dbg.value(metadata i64 %13, metadata !265, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !268
  br label %14, !dbg !277

14:                                               ; preds = %12, %32
  %15 = phi i64 [ %39, %32 ], [ %1, %12 ]
  %16 = phi i64 [ %38, %32 ], [ %0, %12 ]
  %17 = phi i64 [ %42, %32 ], [ %13, %12 ]
  %18 = phi i64 [ %41, %32 ], [ %9, %12 ]
  %19 = phi i8 [ %40, %32 ], [ 1, %12 ]
  call void @llvm.dbg.value(metadata i64 %15, metadata !264, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !268
  call void @llvm.dbg.value(metadata i64 %16, metadata !264, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !268
  call void @llvm.dbg.value(metadata i64 %17, metadata !265, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !268
  call void @llvm.dbg.value(metadata i64 %18, metadata !265, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !268
  call void @llvm.dbg.value(metadata i8 %19, metadata !267, metadata !DIExpression()), !dbg !268
  %20 = and i64 %17, 1, !dbg !278
  %21 = icmp eq i64 %20, 0, !dbg !278
  %22 = zext i8 %19 to i64, !dbg !281
  br i1 %21, label %32, label %23, !dbg !282

23:                                               ; preds = %14
  call void @llvm.dbg.value(metadata i64 %16, metadata !88, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !283
  call void @llvm.dbg.value(metadata i64 %15, metadata !88, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !283
  call void @llvm.dbg.value(metadata i8 %19, metadata !89, metadata !DIExpression()), !dbg !283
  %24 = shl i64 %16, %22, !dbg !285
  %25 = shl i64 %15, %22, !dbg !285
  call void @llvm.dbg.value(metadata i64 %16, metadata !249, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !286
  call void @llvm.dbg.value(metadata i64 %15, metadata !249, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !286
  call void @llvm.dbg.value(metadata i64 %24, metadata !250, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !286
  call void @llvm.dbg.value(metadata i64 %25, metadata !250, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !286
  %26 = or i64 %24, %16, !dbg !288
  call void @llvm.dbg.value(metadata i64 %26, metadata !251, metadata !DIExpression()), !dbg !286
  %27 = or i64 %25, %15, !dbg !289
  %28 = xor i64 %24, %16, !dbg !290
  %29 = or i64 %27, %28, !dbg !291
  call void @llvm.dbg.value(metadata i64 %29, metadata !252, metadata !DIExpression()), !dbg !286
  %30 = xor i64 %29, -1, !dbg !292
  %31 = and i64 %26, %30, !dbg !292
  call void @llvm.dbg.value(metadata i64 %31, metadata !264, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !268
  call void @llvm.dbg.value(metadata i64 %29, metadata !264, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !268
  br label %32, !dbg !293

32:                                               ; preds = %14, %23
  %33 = phi i64 [ %31, %23 ], [ %16, %14 ]
  %34 = phi i64 [ %29, %23 ], [ %15, %14 ]
  call void @llvm.dbg.value(metadata i64 %34, metadata !264, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !268
  call void @llvm.dbg.value(metadata i64 %33, metadata !264, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !268
  %35 = and i64 %18, 1, !dbg !294
  %36 = icmp eq i64 %35, 0, !dbg !294
  %37 = select i1 %36, i64 0, i64 %22, !dbg !296
  %38 = shl i64 %33, %37, !dbg !296
  %39 = shl i64 %34, %37, !dbg !296
  call void @llvm.dbg.value(metadata i64 %39, metadata !264, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !268
  call void @llvm.dbg.value(metadata i64 %38, metadata !264, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !268
  %40 = shl i8 %19, 1, !dbg !297
  call void @llvm.dbg.value(metadata i8 %40, metadata !267, metadata !DIExpression()), !dbg !268
  call void @llvm.dbg.value(metadata i64 %18, metadata !95, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !298
  call void @llvm.dbg.value(metadata i64 %17, metadata !95, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !298
  call void @llvm.dbg.value(metadata i8 1, metadata !96, metadata !DIExpression()), !dbg !298
  %41 = lshr i64 %18, 1, !dbg !300
  %42 = lshr i64 %17, 1, !dbg !300
  call void @llvm.dbg.value(metadata i64 %39, metadata !264, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !268
  call void @llvm.dbg.value(metadata i64 %38, metadata !264, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !268
  call void @llvm.dbg.value(metadata i64 %42, metadata !265, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !268
  call void @llvm.dbg.value(metadata i64 %41, metadata !265, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !268
  %43 = or i64 %42, %41, !dbg !276
  %44 = icmp eq i64 %43, 0, !dbg !276
  br i1 %44, label %45, label %14, !dbg !277, !llvm.loop !301

45:                                               ; preds = %32, %5
  %46 = phi i64 [ %0, %5 ], [ %38, %32 ]
  %47 = phi i64 [ %1, %5 ], [ %39, %32 ]
  %48 = insertvalue { i64, i64 } undef, i64 %46, 0, !dbg !303
  %49 = insertvalue { i64, i64 } %48, i64 %47, 1, !dbg !303
  ret { i64, i64 } %49, !dbg !303
}

; Function Attrs: norecurse noredzone nounwind null_pointer_is_valid readnone sspstrong
define dso_local { i64, i64 } @tnum_lshr(i64 %0, i64 %1, i64 %2, i64 %3, i8 zeroext %4) local_unnamed_addr #2 !dbg !304 {
  call void @llvm.dbg.value(metadata i64 %0, metadata !306, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !310
  call void @llvm.dbg.value(metadata i64 %1, metadata !306, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !310
  call void @llvm.dbg.value(metadata i64 %2, metadata !307, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !310
  call void @llvm.dbg.value(metadata i64 %3, metadata !307, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !310
  call void @llvm.dbg.value(metadata i8 %4, metadata !308, metadata !DIExpression()), !dbg !310
  call void @llvm.dbg.value(metadata i8 1, metadata !309, metadata !DIExpression()), !dbg !310
  %6 = zext i8 %4 to i64, !dbg !311
  %7 = add nsw i64 %6, -1, !dbg !312
  call void @llvm.dbg.value(metadata i64 %2, metadata !157, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !313
  call void @llvm.dbg.value(metadata i64 %3, metadata !157, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !313
  call void @llvm.dbg.value(metadata i64 %7, metadata !158, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !313
  call void @llvm.dbg.value(metadata i64 0, metadata !158, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !313
  %8 = or i64 %3, %2, !dbg !315
  call void @llvm.dbg.value(metadata i64 %8, metadata !159, metadata !DIExpression()), !dbg !313
  call void @llvm.dbg.value(metadata i64 %7, metadata !160, metadata !DIExpression()), !dbg !313
  %9 = and i64 %7, %2, !dbg !316
  call void @llvm.dbg.value(metadata i64 %9, metadata !161, metadata !DIExpression()), !dbg !313
  %10 = and i64 %7, %8, !dbg !317
  call void @llvm.dbg.value(metadata i64 undef, metadata !307, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !310
  call void @llvm.dbg.value(metadata i64 undef, metadata !307, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !310
  call void @llvm.dbg.value(metadata i64 %1, metadata !306, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !310
  call void @llvm.dbg.value(metadata i64 %0, metadata !306, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !310
  call void @llvm.dbg.value(metadata i64 undef, metadata !307, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !310
  call void @llvm.dbg.value(metadata i64 %9, metadata !307, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !310
  call void @llvm.dbg.value(metadata i8 1, metadata !309, metadata !DIExpression()), !dbg !310
  %11 = icmp eq i64 %10, 0, !dbg !318
  br i1 %11, label %45, label %12, !dbg !319

12:                                               ; preds = %5
  %13 = xor i64 %10, %9, !dbg !317
  call void @llvm.dbg.value(metadata i64 %13, metadata !307, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !310
  br label %14, !dbg !319

14:                                               ; preds = %12, %32
  %15 = phi i64 [ %39, %32 ], [ %1, %12 ]
  %16 = phi i64 [ %38, %32 ], [ %0, %12 ]
  %17 = phi i64 [ %42, %32 ], [ %13, %12 ]
  %18 = phi i64 [ %41, %32 ], [ %9, %12 ]
  %19 = phi i8 [ %40, %32 ], [ 1, %12 ]
  call void @llvm.dbg.value(metadata i64 %15, metadata !306, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !310
  call void @llvm.dbg.value(metadata i64 %16, metadata !306, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !310
  call void @llvm.dbg.value(metadata i64 %17, metadata !307, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !310
  call void @llvm.dbg.value(metadata i64 %18, metadata !307, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !310
  call void @llvm.dbg.value(metadata i8 %19, metadata !309, metadata !DIExpression()), !dbg !310
  %20 = and i64 %17, 1, !dbg !320
  %21 = icmp eq i64 %20, 0, !dbg !320
  %22 = zext i8 %19 to i64, !dbg !323
  br i1 %21, label %32, label %23, !dbg !324

23:                                               ; preds = %14
  call void @llvm.dbg.value(metadata i64 %16, metadata !95, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !325
  call void @llvm.dbg.value(metadata i64 %15, metadata !95, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !325
  call void @llvm.dbg.value(metadata i8 %19, metadata !96, metadata !DIExpression()), !dbg !325
  %24 = lshr i64 %16, %22, !dbg !327
  %25 = lshr i64 %15, %22, !dbg !327
  call void @llvm.dbg.value(metadata i64 %16, metadata !249, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !328
  call void @llvm.dbg.value(metadata i64 %15, metadata !249, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !328
  call void @llvm.dbg.value(metadata i64 %24, metadata !250, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !328
  call void @llvm.dbg.value(metadata i64 %25, metadata !250, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !328
  %26 = or i64 %24, %16, !dbg !330
  call void @llvm.dbg.value(metadata i64 %26, metadata !251, metadata !DIExpression()), !dbg !328
  %27 = or i64 %25, %15, !dbg !331
  %28 = xor i64 %24, %16, !dbg !332
  %29 = or i64 %27, %28, !dbg !333
  call void @llvm.dbg.value(metadata i64 %29, metadata !252, metadata !DIExpression()), !dbg !328
  %30 = xor i64 %29, -1, !dbg !334
  %31 = and i64 %26, %30, !dbg !334
  call void @llvm.dbg.value(metadata i64 %31, metadata !306, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !310
  call void @llvm.dbg.value(metadata i64 %29, metadata !306, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !310
  br label %32, !dbg !335

32:                                               ; preds = %14, %23
  %33 = phi i64 [ %31, %23 ], [ %16, %14 ]
  %34 = phi i64 [ %29, %23 ], [ %15, %14 ]
  call void @llvm.dbg.value(metadata i64 %34, metadata !306, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !310
  call void @llvm.dbg.value(metadata i64 %33, metadata !306, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !310
  %35 = and i64 %18, 1, !dbg !336
  %36 = icmp eq i64 %35, 0, !dbg !336
  %37 = select i1 %36, i64 0, i64 %22, !dbg !338
  %38 = lshr i64 %33, %37, !dbg !338
  %39 = lshr i64 %34, %37, !dbg !338
  call void @llvm.dbg.value(metadata i64 %39, metadata !306, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !310
  call void @llvm.dbg.value(metadata i64 %38, metadata !306, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !310
  %40 = shl i8 %19, 1, !dbg !339
  call void @llvm.dbg.value(metadata i8 %40, metadata !309, metadata !DIExpression()), !dbg !310
  call void @llvm.dbg.value(metadata i64 %18, metadata !95, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !340
  call void @llvm.dbg.value(metadata i64 %17, metadata !95, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !340
  call void @llvm.dbg.value(metadata i8 1, metadata !96, metadata !DIExpression()), !dbg !340
  %41 = lshr i64 %18, 1, !dbg !342
  %42 = lshr i64 %17, 1, !dbg !342
  call void @llvm.dbg.value(metadata i64 %39, metadata !306, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !310
  call void @llvm.dbg.value(metadata i64 %38, metadata !306, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !310
  call void @llvm.dbg.value(metadata i64 %42, metadata !307, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !310
  call void @llvm.dbg.value(metadata i64 %41, metadata !307, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !310
  %43 = or i64 %42, %41, !dbg !318
  %44 = icmp eq i64 %43, 0, !dbg !318
  br i1 %44, label %45, label %14, !dbg !319, !llvm.loop !343

45:                                               ; preds = %32, %5
  %46 = phi i64 [ %0, %5 ], [ %38, %32 ]
  %47 = phi i64 [ %1, %5 ], [ %39, %32 ]
  %48 = insertvalue { i64, i64 } undef, i64 %46, 0, !dbg !345
  %49 = insertvalue { i64, i64 } %48, i64 %47, 1, !dbg !345
  ret { i64, i64 } %49, !dbg !345
}

; Function Attrs: norecurse noredzone nounwind null_pointer_is_valid readnone sspstrong willreturn
define dso_local { i64, i64 } @tnum_cast(i64 %0, i64 %1, i8 zeroext %2) local_unnamed_addr #0 !dbg !346 {
  call void @llvm.dbg.value(metadata i64 %0, metadata !348, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !350
  call void @llvm.dbg.value(metadata i64 %1, metadata !348, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !350
  call void @llvm.dbg.value(metadata i8 %2, metadata !349, metadata !DIExpression()), !dbg !350
  %4 = zext i8 %2 to i64, !dbg !351
  %5 = shl nuw nsw i64 %4, 3, !dbg !352
  %6 = shl nsw i64 -1, %5, !dbg !353
  %7 = xor i64 %6, -1, !dbg !353
  %8 = and i64 %7, %0, !dbg !354
  call void @llvm.dbg.value(metadata i64 %8, metadata !348, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !350
  %9 = and i64 %7, %1, !dbg !355
  call void @llvm.dbg.value(metadata i64 %9, metadata !348, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !350
  %10 = insertvalue { i64, i64 } undef, i64 %8, 0, !dbg !356
  %11 = insertvalue { i64, i64 } %10, i64 %9, 1, !dbg !356
  ret { i64, i64 } %11, !dbg !356
}

; Function Attrs: norecurse noredzone nounwind null_pointer_is_valid readnone sspstrong willreturn
define dso_local zeroext i1 @tnum_is_aligned(i64 %0, i64 %1, i64 %2) local_unnamed_addr #0 !dbg !357 {
  call void @llvm.dbg.value(metadata i64 %0, metadata !363, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !365
  call void @llvm.dbg.value(metadata i64 %1, metadata !363, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !365
  call void @llvm.dbg.value(metadata i64 %2, metadata !364, metadata !DIExpression()), !dbg !365
  %4 = icmp eq i64 %2, 0, !dbg !366
  %5 = or i64 %1, %0, !dbg !368
  %6 = add i64 %2, -1, !dbg !368
  %7 = and i64 %6, %5, !dbg !368
  %8 = icmp eq i64 %7, 0, !dbg !368
  %9 = or i1 %4, %8, !dbg !368
  ret i1 %9, !dbg !369
}

; Function Attrs: norecurse noredzone nounwind null_pointer_is_valid readnone sspstrong willreturn
define dso_local zeroext i1 @tnum_in(i64 %0, i64 %1, i64 %2, i64 %3) local_unnamed_addr #0 !dbg !370 {
  call void @llvm.dbg.value(metadata i64 %0, metadata !374, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !376
  call void @llvm.dbg.value(metadata i64 %1, metadata !374, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !376
  call void @llvm.dbg.value(metadata i64 %2, metadata !375, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !376
  call void @llvm.dbg.value(metadata i64 %3, metadata !375, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !376
  %5 = xor i64 %1, -1, !dbg !377
  %6 = and i64 %5, %3, !dbg !379
  %7 = icmp eq i64 %6, 0, !dbg !379
  %8 = and i64 %5, %2, !dbg !380
  %9 = icmp eq i64 %8, %0, !dbg !380
  %10 = and i1 %9, %7, !dbg !380
  ret i1 %10, !dbg !381
}

; Function Attrs: nofree noredzone nounwind null_pointer_is_valid sspstrong
define dso_local i32 @tnum_strn(i8* nocapture %0, i64 %1, i64 %2, i64 %3) #3 !dbg !382 {
  call void @llvm.dbg.value(metadata i64 %2, metadata !390, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !391
  call void @llvm.dbg.value(metadata i64 %3, metadata !390, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !391
  call void @llvm.dbg.value(metadata i8* %0, metadata !388, metadata !DIExpression()), !dbg !391
  call void @llvm.dbg.value(metadata i64 %1, metadata !389, metadata !DIExpression()), !dbg !391
  %5 = tail call i32 (i8*, i64, i8*, ...) @snprintf(i8* %0, i64 %1, i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str, i64 0, i64 0), i64 %2, i64 %3) #9, !dbg !392
  ret i32 %5, !dbg !393
}

; Function Attrs: nofree noredzone nounwind null_pointer_is_valid
declare dso_local noundef i32 @snprintf(i8* noalias nocapture noundef writeonly, i64 noundef, i8* nocapture noundef readonly, ...) local_unnamed_addr #4

; Function Attrs: nofree norecurse noredzone nounwind null_pointer_is_valid sspstrong writeonly
define dso_local i32 @tnum_sbin(i8* nocapture %0, i64 %1, i64 %2, i64 %3) local_unnamed_addr #5 !dbg !394 {
  call void @llvm.dbg.value(metadata i64 %2, metadata !398, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !403
  call void @llvm.dbg.value(metadata i64 %3, metadata !398, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !403
  call void @llvm.dbg.value(metadata i8* %0, metadata !396, metadata !DIExpression()), !dbg !403
  call void @llvm.dbg.value(metadata i64 %1, metadata !397, metadata !DIExpression()), !dbg !403
  call void @llvm.dbg.value(metadata i64 64, metadata !399, metadata !DIExpression()), !dbg !403
  br label %5, !dbg !404

5:                                                ; preds = %4, %25
  %6 = phi i64 [ %3, %4 ], [ %27, %25 ]
  %7 = phi i64 [ %2, %4 ], [ %28, %25 ]
  %8 = phi i64 [ 64, %4 ], [ %26, %25 ]
  call void @llvm.dbg.value(metadata i64 %6, metadata !398, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !403
  call void @llvm.dbg.value(metadata i64 %7, metadata !398, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !403
  call void @llvm.dbg.value(metadata i64 %8, metadata !399, metadata !DIExpression()), !dbg !403
  %9 = icmp ult i64 %8, %1, !dbg !406
  br i1 %9, label %12, label %10, !dbg !410

10:                                               ; preds = %5
  %11 = add nsw i64 %8, -1, !dbg !411
  br label %25, !dbg !410

12:                                               ; preds = %5
  %13 = and i64 %6, 1, !dbg !412
  %14 = icmp eq i64 %13, 0, !dbg !412
  br i1 %14, label %18, label %15, !dbg !415

15:                                               ; preds = %12
  %16 = add nsw i64 %8, -1, !dbg !416
  %17 = getelementptr i8, i8* %0, i64 %16, !dbg !417
  store i8 120, i8* %17, align 1, !dbg !418
  br label %25, !dbg !417

18:                                               ; preds = %12
  %19 = and i64 %7, 1, !dbg !419
  %20 = icmp eq i64 %19, 0, !dbg !419
  %21 = add nsw i64 %8, -1, !dbg !421
  %22 = getelementptr i8, i8* %0, i64 %21, !dbg !421
  br i1 %20, label %24, label %23, !dbg !422

23:                                               ; preds = %18
  store i8 49, i8* %22, align 1, !dbg !423
  br label %25, !dbg !424

24:                                               ; preds = %18
  store i8 48, i8* %22, align 1, !dbg !425
  br label %25

25:                                               ; preds = %10, %15, %24, %23
  %26 = phi i64 [ %11, %10 ], [ %16, %15 ], [ %21, %24 ], [ %21, %23 ], !dbg !411
  %27 = lshr i64 %6, 1, !dbg !426
  call void @llvm.dbg.value(metadata i64 %27, metadata !398, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !403
  %28 = lshr i64 %7, 1, !dbg !427
  call void @llvm.dbg.value(metadata i64 %28, metadata !398, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !403
  call void @llvm.dbg.value(metadata i64 %27, metadata !398, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !403
  call void @llvm.dbg.value(metadata i64 %28, metadata !398, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !403
  call void @llvm.dbg.value(metadata i64 %26, metadata !399, metadata !DIExpression()), !dbg !403
  %29 = icmp eq i64 %26, 0, !dbg !404
  br i1 %29, label %30, label %5, !dbg !404, !llvm.loop !428

30:                                               ; preds = %25
  %31 = add i64 %1, -1, !dbg !430
  call void @llvm.dbg.value(metadata i64 %31, metadata !400, metadata !DIExpression()), !dbg !431
  call void @llvm.dbg.value(metadata i64 64, metadata !402, metadata !DIExpression()), !dbg !431
  %32 = icmp ult i64 %31, 64, !dbg !430
  %33 = select i1 %32, i64 %31, i64 64, !dbg !430
  %34 = getelementptr i8, i8* %0, i64 %33, !dbg !432
  store i8 0, i8* %34, align 1, !dbg !433
  ret i32 64, !dbg !434
}

; Function Attrs: norecurse noredzone nounwind null_pointer_is_valid readnone sspstrong willreturn
define dso_local { i64, i64 } @tnum_subreg(i64 %0, i64 %1) local_unnamed_addr #0 !dbg !435 {
  call void @llvm.dbg.value(metadata i64 %0, metadata !439, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !440
  call void @llvm.dbg.value(metadata i64 %1, metadata !439, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !440
  call void @llvm.dbg.value(metadata i64 %0, metadata !348, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !441
  call void @llvm.dbg.value(metadata i64 %1, metadata !348, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !441
  call void @llvm.dbg.value(metadata i8 4, metadata !349, metadata !DIExpression()), !dbg !441
  %3 = and i64 %0, 4294967295, !dbg !443
  call void @llvm.dbg.value(metadata i64 %3, metadata !348, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !441
  %4 = and i64 %1, 4294967295, !dbg !444
  call void @llvm.dbg.value(metadata i64 %4, metadata !348, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !441
  %5 = insertvalue { i64, i64 } undef, i64 %3, 0, !dbg !445
  %6 = insertvalue { i64, i64 } %5, i64 %4, 1, !dbg !445
  ret { i64, i64 } %6, !dbg !446
}

; Function Attrs: norecurse noredzone nounwind null_pointer_is_valid readnone sspstrong willreturn
define dso_local { i64, i64 } @tnum_clear_subreg(i64 %0, i64 %1) local_unnamed_addr #0 !dbg !447 {
  call void @llvm.dbg.value(metadata i64 %0, metadata !449, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !450
  call void @llvm.dbg.value(metadata i64 %1, metadata !449, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !450
  %3 = and i64 %0, -4294967296, !dbg !451
  %4 = and i64 %1, -4294967296, !dbg !451
  call void @llvm.dbg.value(metadata i64 %0, metadata !88, metadata !DIExpression(DW_OP_constu, 32, DW_OP_shr, DW_OP_stack_value, DW_OP_LLVM_fragment, 0, 64)), !dbg !453
  call void @llvm.dbg.value(metadata i64 %1, metadata !88, metadata !DIExpression(DW_OP_constu, 32, DW_OP_shr, DW_OP_stack_value, DW_OP_LLVM_fragment, 64, 64)), !dbg !453
  call void @llvm.dbg.value(metadata i8 32, metadata !89, metadata !DIExpression()), !dbg !453
  %5 = insertvalue { i64, i64 } undef, i64 %3, 0, !dbg !454
  %6 = insertvalue { i64, i64 } %5, i64 %4, 1, !dbg !454
  ret { i64, i64 } %6, !dbg !455
}

; Function Attrs: norecurse noredzone nounwind null_pointer_is_valid readnone sspstrong willreturn
define dso_local { i64, i64 } @tnum_const_subreg(i64 %0, i64 %1, i32 %2) local_unnamed_addr #0 !dbg !456 {
  call void @llvm.dbg.value(metadata i64 %0, metadata !460, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !462
  call void @llvm.dbg.value(metadata i64 %1, metadata !460, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !462
  call void @llvm.dbg.value(metadata i32 %2, metadata !461, metadata !DIExpression()), !dbg !462
  call void @llvm.dbg.value(metadata i64 %0, metadata !449, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !463
  call void @llvm.dbg.value(metadata i64 %1, metadata !449, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !463
  %4 = and i64 %0, -4294967296, !dbg !465
  %5 = and i64 %1, -4294967296, !dbg !465
  call void @llvm.dbg.value(metadata i64 %0, metadata !88, metadata !DIExpression(DW_OP_constu, 32, DW_OP_shr, DW_OP_stack_value, DW_OP_LLVM_fragment, 0, 64)), !dbg !467
  call void @llvm.dbg.value(metadata i64 %1, metadata !88, metadata !DIExpression(DW_OP_constu, 32, DW_OP_shr, DW_OP_stack_value, DW_OP_LLVM_fragment, 64, 64)), !dbg !467
  call void @llvm.dbg.value(metadata i8 32, metadata !89, metadata !DIExpression()), !dbg !467
  %6 = zext i32 %2 to i64, !dbg !468
  call void @llvm.dbg.value(metadata i64 %4, metadata !170, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !469
  call void @llvm.dbg.value(metadata i64 %5, metadata !170, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !469
  call void @llvm.dbg.value(metadata i64 %6, metadata !171, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 64)), !dbg !469
  call void @llvm.dbg.value(metadata i64 0, metadata !171, metadata !DIExpression(DW_OP_LLVM_fragment, 64, 64)), !dbg !469
  %7 = or i64 %4, %6, !dbg !471
  call void @llvm.dbg.value(metadata i64 %7, metadata !172, metadata !DIExpression()), !dbg !469
  call void @llvm.dbg.value(metadata i64 %5, metadata !173, metadata !DIExpression()), !dbg !469
  %8 = xor i64 %7, -1, !dbg !472
  %9 = and i64 %5, %8, !dbg !472
  %10 = insertvalue { i64, i64 } undef, i64 %7, 0, !dbg !473
  %11 = insertvalue { i64, i64 } %10, i64 %9, 1, !dbg !473
  ret { i64, i64 } %11, !dbg !474
}

; Function Attrs: nofree nosync nounwind readnone speculatable willreturn
declare void @llvm.dbg.value(metadata, metadata, metadata) #6

attributes #0 = { norecurse noredzone nounwind null_pointer_is_valid readnone sspstrong willreturn "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+retpoline-external-thunk,+retpoline-indirect-branches,+retpoline-indirect-calls,-3dnow,-3dnowa,-aes,-avx,-avx2,-avx512bf16,-avx512bitalg,-avx512bw,-avx512cd,-avx512dq,-avx512er,-avx512f,-avx512ifma,-avx512pf,-avx512vbmi,-avx512vbmi2,-avx512vl,-avx512vnni,-avx512vp2intersect,-avx512vpopcntdq,-avxvnni,-f16c,-fma,-fma4,-gfni,-kl,-mmx,-pclmul,-sha,-sse,-sse2,-sse3,-sse4.1,-sse4.2,-sse4a,-ssse3,-vaes,-vpclmulqdq,-widekl,-x87,-xop" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noredzone nounwind null_pointer_is_valid readonly sspstrong "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+retpoline-external-thunk,+retpoline-indirect-branches,+retpoline-indirect-calls,-3dnow,-3dnowa,-aes,-avx,-avx2,-avx512bf16,-avx512bitalg,-avx512bw,-avx512cd,-avx512dq,-avx512er,-avx512f,-avx512ifma,-avx512pf,-avx512vbmi,-avx512vbmi2,-avx512vl,-avx512vnni,-avx512vp2intersect,-avx512vpopcntdq,-avxvnni,-f16c,-fma,-fma4,-gfni,-kl,-mmx,-pclmul,-sha,-sse,-sse2,-sse3,-sse4.1,-sse4.2,-sse4a,-ssse3,-vaes,-vpclmulqdq,-widekl,-x87,-xop" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { norecurse noredzone nounwind null_pointer_is_valid readnone sspstrong "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+retpoline-external-thunk,+retpoline-indirect-branches,+retpoline-indirect-calls,-3dnow,-3dnowa,-aes,-avx,-avx2,-avx512bf16,-avx512bitalg,-avx512bw,-avx512cd,-avx512dq,-avx512er,-avx512f,-avx512ifma,-avx512pf,-avx512vbmi,-avx512vbmi2,-avx512vl,-avx512vnni,-avx512vp2intersect,-avx512vpopcntdq,-avxvnni,-f16c,-fma,-fma4,-gfni,-kl,-mmx,-pclmul,-sha,-sse,-sse2,-sse3,-sse4.1,-sse4.2,-sse4a,-ssse3,-vaes,-vpclmulqdq,-widekl,-x87,-xop" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nofree noredzone nounwind null_pointer_is_valid sspstrong "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+retpoline-external-thunk,+retpoline-indirect-branches,+retpoline-indirect-calls,-3dnow,-3dnowa,-aes,-avx,-avx2,-avx512bf16,-avx512bitalg,-avx512bw,-avx512cd,-avx512dq,-avx512er,-avx512f,-avx512ifma,-avx512pf,-avx512vbmi,-avx512vbmi2,-avx512vl,-avx512vnni,-avx512vp2intersect,-avx512vpopcntdq,-avxvnni,-f16c,-fma,-fma4,-gfni,-kl,-mmx,-pclmul,-sha,-sse,-sse2,-sse3,-sse4.1,-sse4.2,-sse4a,-ssse3,-vaes,-vpclmulqdq,-widekl,-x87,-xop" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { nofree noredzone nounwind null_pointer_is_valid "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+retpoline-external-thunk,+retpoline-indirect-branches,+retpoline-indirect-calls,-3dnow,-3dnowa,-aes,-avx,-avx2,-avx512bf16,-avx512bitalg,-avx512bw,-avx512cd,-avx512dq,-avx512er,-avx512f,-avx512ifma,-avx512pf,-avx512vbmi,-avx512vbmi2,-avx512vl,-avx512vnni,-avx512vp2intersect,-avx512vpopcntdq,-avxvnni,-f16c,-fma,-fma4,-gfni,-kl,-mmx,-pclmul,-sha,-sse,-sse2,-sse3,-sse4.1,-sse4.2,-sse4a,-ssse3,-vaes,-vpclmulqdq,-widekl,-x87,-xop" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { nofree norecurse noredzone nounwind null_pointer_is_valid sspstrong writeonly "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+retpoline-external-thunk,+retpoline-indirect-branches,+retpoline-indirect-calls,-3dnow,-3dnowa,-aes,-avx,-avx2,-avx512bf16,-avx512bitalg,-avx512bw,-avx512cd,-avx512dq,-avx512er,-avx512f,-avx512ifma,-avx512pf,-avx512vbmi,-avx512vbmi2,-avx512vl,-avx512vnni,-avx512vp2intersect,-avx512vpopcntdq,-avxvnni,-f16c,-fma,-fma4,-gfni,-kl,-mmx,-pclmul,-sha,-sse,-sse2,-sse3,-sse4.1,-sse4.2,-sse4a,-ssse3,-vaes,-vpclmulqdq,-widekl,-x87,-xop" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #6 = { nofree nosync nounwind readnone speculatable willreturn }
attributes #7 = { nounwind }
attributes #8 = { nounwind readonly }
attributes #9 = { noredzone }

!llvm.dbg.cu = !{!2}
!llvm.module.flags = !{!41, !42, !43, !44}
!llvm.ident = !{!45}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(name: "tnum_unknown", scope: !2, file: !3, line: 14, type: !32, isLocal: false, isDefinition: true)
!2 = distinct !DICompileUnit(language: DW_LANG_C89, file: !3, producer: "Ubuntu clang version 12.0.0-3ubuntu1~20.04.4", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug, enums: !4, retainedTypes: !11, globals: !28, splitDebugInlining: false, nameTableKind: None)
!3 = !DIFile(filename: "kernel/bpf/tnum.c", directory: "/home/lukenels/repo/linux")
!4 = !{!5}
!5 = !DICompositeType(tag: DW_TAG_enumeration_type, file: !6, line: 10, baseType: !7, size: 32, elements: !8)
!6 = !DIFile(filename: "./include/linux/stddef.h", directory: "/home/lukenels/repo/linux")
!7 = !DIBasicType(name: "unsigned int", size: 32, encoding: DW_ATE_unsigned)
!8 = !{!9, !10}
!9 = !DIEnumerator(name: "false", value: 0, isUnsigned: true)
!10 = !DIEnumerator(name: "true", value: 1, isUnsigned: true)
!11 = !{!12, !16, !19, !22}
!12 = !DIDerivedType(tag: DW_TAG_typedef, name: "u32", file: !13, line: 21, baseType: !14)
!13 = !DIFile(filename: "./include/asm-generic/int-ll64.h", directory: "/home/lukenels/repo/linux")
!14 = !DIDerivedType(tag: DW_TAG_typedef, name: "__u32", file: !15, line: 27, baseType: !7)
!15 = !DIFile(filename: "./include/uapi/asm-generic/int-ll64.h", directory: "/home/lukenels/repo/linux")
!16 = !DIDerivedType(tag: DW_TAG_typedef, name: "s32", file: !13, line: 20, baseType: !17)
!17 = !DIDerivedType(tag: DW_TAG_typedef, name: "__s32", file: !15, line: 26, baseType: !18)
!18 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!19 = !DIDerivedType(tag: DW_TAG_typedef, name: "s64", file: !13, line: 22, baseType: !20)
!20 = !DIDerivedType(tag: DW_TAG_typedef, name: "__s64", file: !15, line: 30, baseType: !21)
!21 = !DIBasicType(name: "long long int", size: 64, encoding: DW_ATE_signed)
!22 = !DIDerivedType(tag: DW_TAG_typedef, name: "size_t", file: !23, line: 55, baseType: !24)
!23 = !DIFile(filename: "./include/linux/types.h", directory: "/home/lukenels/repo/linux")
!24 = !DIDerivedType(tag: DW_TAG_typedef, name: "__kernel_size_t", file: !25, line: 72, baseType: !26)
!25 = !DIFile(filename: "./include/uapi/asm-generic/posix_types.h", directory: "/home/lukenels/repo/linux")
!26 = !DIDerivedType(tag: DW_TAG_typedef, name: "__kernel_ulong_t", file: !25, line: 16, baseType: !27)
!27 = !DIBasicType(name: "long unsigned int", size: 64, encoding: DW_ATE_unsigned)
!28 = !{!0, !29}
!29 = !DIGlobalVariableExpression(var: !30, expr: !DIExpression())
!30 = distinct !DIGlobalVariable(name: "__UNIQUE_ID___addressable_tnum_strn1", scope: !2, file: !3, line: 228, type: !31, isLocal: true, isDefinition: true)
!31 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: null, size: 64)
!32 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !33)
!33 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "tnum", file: !34, line: 14, size: 128, elements: !35)
!34 = !DIFile(filename: "./include/linux/tnum.h", directory: "/home/lukenels/repo/linux")
!35 = !{!36, !40}
!36 = !DIDerivedType(tag: DW_TAG_member, name: "value", scope: !33, file: !34, line: 15, baseType: !37, size: 64)
!37 = !DIDerivedType(tag: DW_TAG_typedef, name: "u64", file: !13, line: 23, baseType: !38)
!38 = !DIDerivedType(tag: DW_TAG_typedef, name: "__u64", file: !15, line: 31, baseType: !39)
!39 = !DIBasicType(name: "long long unsigned int", size: 64, encoding: DW_ATE_unsigned)
!40 = !DIDerivedType(tag: DW_TAG_member, name: "mask", scope: !33, file: !34, line: 16, baseType: !37, size: 64, offset: 64)
!41 = !{i32 7, !"Dwarf Version", i32 4}
!42 = !{i32 2, !"Debug Info Version", i32 3}
!43 = !{i32 1, !"wchar_size", i32 2}
!44 = !{i32 1, !"Code Model", i32 2}
!45 = !{!"Ubuntu clang version 12.0.0-3ubuntu1~20.04.4"}
!46 = distinct !DISubprogram(name: "tnum_const", scope: !3, file: !3, line: 16, type: !47, scopeLine: 17, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !49)
!47 = !DISubroutineType(types: !48)
!48 = !{!33, !37}
!49 = !{!50}
!50 = !DILocalVariable(name: "value", arg: 1, scope: !46, file: !3, line: 16, type: !37)
!51 = !DILocation(line: 0, scope: !46)
!52 = !DILocation(line: 18, column: 2, scope: !46)
!53 = distinct !DISubprogram(name: "tnum_range", scope: !3, file: !3, line: 21, type: !54, scopeLine: 22, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !56)
!54 = !DISubroutineType(types: !55)
!55 = !{!33, !37, !37}
!56 = !{!57, !58, !59, !60, !61}
!57 = !DILocalVariable(name: "min", arg: 1, scope: !53, file: !3, line: 21, type: !37)
!58 = !DILocalVariable(name: "max", arg: 2, scope: !53, file: !3, line: 21, type: !37)
!59 = !DILocalVariable(name: "chi", scope: !53, file: !3, line: 23, type: !37)
!60 = !DILocalVariable(name: "delta", scope: !53, file: !3, line: 23, type: !37)
!61 = !DILocalVariable(name: "bits", scope: !53, file: !3, line: 24, type: !62)
!62 = !DIDerivedType(tag: DW_TAG_typedef, name: "u8", file: !13, line: 17, baseType: !63)
!63 = !DIDerivedType(tag: DW_TAG_typedef, name: "__u8", file: !15, line: 21, baseType: !64)
!64 = !DIBasicType(name: "unsigned char", size: 8, encoding: DW_ATE_unsigned_char)
!65 = !DILocation(line: 0, scope: !53)
!66 = !DILocation(line: 23, column: 16, scope: !53)
!67 = !DILocalVariable(name: "x", arg: 1, scope: !68, file: !69, line: 366, type: !38)
!68 = distinct !DISubprogram(name: "fls64", scope: !69, file: !69, line: 366, type: !70, scopeLine: 367, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !72)
!69 = !DIFile(filename: "./arch/x86/include/asm/bitops.h", directory: "/home/lukenels/repo/linux")
!70 = !DISubroutineType(types: !71)
!71 = !{!18, !38}
!72 = !{!67, !73}
!73 = !DILocalVariable(name: "bitpos", scope: !68, file: !69, line: 368, type: !18)
!74 = !DILocation(line: 0, scope: !68, inlinedAt: !75)
!75 = distinct !DILocation(line: 24, column: 12, scope: !53)
!76 = !DILocation(line: 374, column: 2, scope: !68, inlinedAt: !75)
!77 = !{i32 229394}
!78 = !DILocation(line: 377, column: 16, scope: !68, inlinedAt: !75)
!79 = !DILocation(line: 27, column: 6, scope: !80)
!80 = distinct !DILexicalBlock(scope: !53, file: !3, line: 27, column: 6)
!81 = !DILocation(line: 27, column: 11, scope: !80)
!82 = !DILocation(line: 27, column: 6, scope: !53)
!83 = !DILocation(line: 35, column: 1, scope: !53)
!84 = distinct !DISubprogram(name: "tnum_lshift", scope: !3, file: !3, line: 37, type: !85, scopeLine: 38, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !87)
!85 = !DISubroutineType(types: !86)
!86 = !{!33, !33, !62}
!87 = !{!88, !89}
!88 = !DILocalVariable(name: "a", arg: 1, scope: !84, file: !3, line: 37, type: !33)
!89 = !DILocalVariable(name: "shift", arg: 2, scope: !84, file: !3, line: 37, type: !62)
!90 = !DILocation(line: 0, scope: !84)
!91 = !DILocation(line: 39, column: 9, scope: !84)
!92 = !DILocation(line: 39, column: 2, scope: !84)
!93 = distinct !DISubprogram(name: "tnum_rshift", scope: !3, file: !3, line: 42, type: !85, scopeLine: 43, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !94)
!94 = !{!95, !96}
!95 = !DILocalVariable(name: "a", arg: 1, scope: !93, file: !3, line: 42, type: !33)
!96 = !DILocalVariable(name: "shift", arg: 2, scope: !93, file: !3, line: 42, type: !62)
!97 = !DILocation(line: 0, scope: !93)
!98 = !DILocation(line: 44, column: 9, scope: !93)
!99 = !DILocation(line: 44, column: 2, scope: !93)
!100 = distinct !DISubprogram(name: "tnum_arshift", scope: !3, file: !3, line: 47, type: !101, scopeLine: 48, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !103)
!101 = !DISubroutineType(types: !102)
!102 = !{!33, !33, !62, !62}
!103 = !{!104, !105, !106}
!104 = !DILocalVariable(name: "a", arg: 1, scope: !100, file: !3, line: 47, type: !33)
!105 = !DILocalVariable(name: "min_shift", arg: 2, scope: !100, file: !3, line: 47, type: !62)
!106 = !DILocalVariable(name: "insn_bitness", arg: 3, scope: !100, file: !3, line: 47, type: !62)
!107 = !DILocation(line: 0, scope: !100)
!108 = !DILocation(line: 54, column: 19, scope: !109)
!109 = distinct !DILexicalBlock(scope: !100, file: !3, line: 54, column: 6)
!110 = !DILocation(line: 54, column: 6, scope: !100)
!111 = !DILocation(line: 55, column: 10, scope: !109)
!112 = !DILocation(line: 55, column: 3, scope: !109)
!113 = !DILocation(line: 58, column: 10, scope: !109)
!114 = !DILocation(line: 58, column: 3, scope: !109)
!115 = !DILocation(line: 0, scope: !109)
!116 = !DILocation(line: 60, column: 1, scope: !100)
!117 = distinct !DISubprogram(name: "tnum_add", scope: !3, file: !3, line: 62, type: !118, scopeLine: 63, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !120)
!118 = !DISubroutineType(types: !119)
!119 = !{!33, !33, !33}
!120 = !{!121, !122, !123, !124, !125, !126, !127}
!121 = !DILocalVariable(name: "a", arg: 1, scope: !117, file: !3, line: 62, type: !33)
!122 = !DILocalVariable(name: "b", arg: 2, scope: !117, file: !3, line: 62, type: !33)
!123 = !DILocalVariable(name: "sm", scope: !117, file: !3, line: 64, type: !37)
!124 = !DILocalVariable(name: "sv", scope: !117, file: !3, line: 64, type: !37)
!125 = !DILocalVariable(name: "sigma", scope: !117, file: !3, line: 64, type: !37)
!126 = !DILocalVariable(name: "chi", scope: !117, file: !3, line: 64, type: !37)
!127 = !DILocalVariable(name: "mu", scope: !117, file: !3, line: 64, type: !37)
!128 = !DILocation(line: 0, scope: !117)
!129 = !DILocation(line: 66, column: 14, scope: !117)
!130 = !DILocation(line: 67, column: 15, scope: !117)
!131 = !DILocation(line: 68, column: 13, scope: !117)
!132 = !DILocation(line: 69, column: 14, scope: !117)
!133 = !DILocation(line: 70, column: 11, scope: !117)
!134 = !DILocation(line: 70, column: 20, scope: !117)
!135 = !DILocation(line: 71, column: 9, scope: !117)
!136 = !DILocation(line: 72, column: 1, scope: !117)
!137 = distinct !DISubprogram(name: "tnum_sub", scope: !3, file: !3, line: 74, type: !118, scopeLine: 75, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !138)
!138 = !{!139, !140, !141, !142, !143, !144, !145}
!139 = !DILocalVariable(name: "a", arg: 1, scope: !137, file: !3, line: 74, type: !33)
!140 = !DILocalVariable(name: "b", arg: 2, scope: !137, file: !3, line: 74, type: !33)
!141 = !DILocalVariable(name: "dv", scope: !137, file: !3, line: 76, type: !37)
!142 = !DILocalVariable(name: "alpha", scope: !137, file: !3, line: 76, type: !37)
!143 = !DILocalVariable(name: "beta", scope: !137, file: !3, line: 76, type: !37)
!144 = !DILocalVariable(name: "chi", scope: !137, file: !3, line: 76, type: !37)
!145 = !DILocalVariable(name: "mu", scope: !137, file: !3, line: 76, type: !37)
!146 = !DILocation(line: 0, scope: !137)
!147 = !DILocation(line: 78, column: 15, scope: !137)
!148 = !DILocation(line: 79, column: 13, scope: !137)
!149 = !DILocation(line: 80, column: 12, scope: !137)
!150 = !DILocation(line: 81, column: 14, scope: !137)
!151 = !DILocation(line: 82, column: 11, scope: !137)
!152 = !DILocation(line: 82, column: 20, scope: !137)
!153 = !DILocation(line: 83, column: 9, scope: !137)
!154 = !DILocation(line: 84, column: 1, scope: !137)
!155 = distinct !DISubprogram(name: "tnum_and", scope: !3, file: !3, line: 86, type: !118, scopeLine: 87, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !156)
!156 = !{!157, !158, !159, !160, !161}
!157 = !DILocalVariable(name: "a", arg: 1, scope: !155, file: !3, line: 86, type: !33)
!158 = !DILocalVariable(name: "b", arg: 2, scope: !155, file: !3, line: 86, type: !33)
!159 = !DILocalVariable(name: "alpha", scope: !155, file: !3, line: 88, type: !37)
!160 = !DILocalVariable(name: "beta", scope: !155, file: !3, line: 88, type: !37)
!161 = !DILocalVariable(name: "v", scope: !155, file: !3, line: 88, type: !37)
!162 = !DILocation(line: 0, scope: !155)
!163 = !DILocation(line: 90, column: 18, scope: !155)
!164 = !DILocation(line: 91, column: 17, scope: !155)
!165 = !DILocation(line: 92, column: 14, scope: !155)
!166 = !DILocation(line: 93, column: 9, scope: !155)
!167 = !DILocation(line: 94, column: 1, scope: !155)
!168 = distinct !DISubprogram(name: "tnum_or", scope: !3, file: !3, line: 96, type: !118, scopeLine: 97, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !169)
!169 = !{!170, !171, !172, !173}
!170 = !DILocalVariable(name: "a", arg: 1, scope: !168, file: !3, line: 96, type: !33)
!171 = !DILocalVariable(name: "b", arg: 2, scope: !168, file: !3, line: 96, type: !33)
!172 = !DILocalVariable(name: "v", scope: !168, file: !3, line: 98, type: !37)
!173 = !DILocalVariable(name: "mu", scope: !168, file: !3, line: 98, type: !37)
!174 = !DILocation(line: 0, scope: !168)
!175 = !DILocation(line: 100, column: 14, scope: !168)
!176 = !DILocation(line: 101, column: 14, scope: !168)
!177 = !DILocation(line: 102, column: 9, scope: !168)
!178 = !DILocation(line: 103, column: 1, scope: !168)
!179 = distinct !DISubprogram(name: "tnum_xor", scope: !3, file: !3, line: 105, type: !118, scopeLine: 106, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !180)
!180 = !{!181, !182, !183, !184}
!181 = !DILocalVariable(name: "a", arg: 1, scope: !179, file: !3, line: 105, type: !33)
!182 = !DILocalVariable(name: "b", arg: 2, scope: !179, file: !3, line: 105, type: !33)
!183 = !DILocalVariable(name: "v", scope: !179, file: !3, line: 107, type: !37)
!184 = !DILocalVariable(name: "mu", scope: !179, file: !3, line: 107, type: !37)
!185 = !DILocation(line: 0, scope: !179)
!186 = !DILocation(line: 109, column: 14, scope: !179)
!187 = !DILocation(line: 110, column: 14, scope: !179)
!188 = !DILocation(line: 111, column: 9, scope: !179)
!189 = !DILocation(line: 112, column: 1, scope: !179)
!190 = distinct !DISubprogram(name: "tnum_mul", scope: !3, file: !3, line: 122, type: !118, scopeLine: 123, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !191)
!191 = !{!192, !193, !194, !195}
!192 = !DILocalVariable(name: "a", arg: 1, scope: !190, file: !3, line: 122, type: !33)
!193 = !DILocalVariable(name: "b", arg: 2, scope: !190, file: !3, line: 122, type: !33)
!194 = !DILocalVariable(name: "acc_v", scope: !190, file: !3, line: 124, type: !37)
!195 = !DILocalVariable(name: "acc_m", scope: !190, file: !3, line: 125, type: !33)
!196 = !DILocation(line: 0, scope: !190)
!197 = !DILocation(line: 127, column: 17, scope: !190)
!198 = !DILocation(line: 127, column: 2, scope: !190)
!199 = !DILocation(line: 129, column: 15, scope: !200)
!200 = distinct !DILexicalBlock(scope: !201, file: !3, line: 129, column: 7)
!201 = distinct !DILexicalBlock(scope: !190, file: !3, line: 127, column: 28)
!202 = !DILocation(line: 129, column: 7, scope: !201)
!203 = !DILocation(line: 0, scope: !117, inlinedAt: !204)
!204 = distinct !DILocation(line: 130, column: 12, scope: !200)
!205 = !DILocation(line: 68, column: 13, scope: !117, inlinedAt: !204)
!206 = !DILocation(line: 70, column: 11, scope: !117, inlinedAt: !204)
!207 = !DILocation(line: 70, column: 20, scope: !117, inlinedAt: !204)
!208 = !DILocation(line: 130, column: 4, scope: !200)
!209 = !DILocation(line: 132, column: 19, scope: !210)
!210 = distinct !DILexicalBlock(scope: !200, file: !3, line: 132, column: 12)
!211 = !DILocation(line: 132, column: 12, scope: !200)
!212 = !DILocation(line: 133, column: 28, scope: !210)
!213 = !DILocation(line: 0, scope: !117, inlinedAt: !214)
!214 = distinct !DILocation(line: 133, column: 12, scope: !210)
!215 = !DILocation(line: 68, column: 13, scope: !117, inlinedAt: !214)
!216 = !DILocation(line: 70, column: 11, scope: !117, inlinedAt: !214)
!217 = !DILocation(line: 70, column: 20, scope: !117, inlinedAt: !214)
!218 = !DILocation(line: 133, column: 4, scope: !210)
!219 = !DILocation(line: 0, scope: !93, inlinedAt: !220)
!220 = distinct !DILocation(line: 135, column: 7, scope: !201)
!221 = !DILocation(line: 44, column: 9, scope: !93, inlinedAt: !220)
!222 = !DILocation(line: 0, scope: !84, inlinedAt: !223)
!223 = distinct !DILocation(line: 136, column: 7, scope: !201)
!224 = !DILocation(line: 39, column: 9, scope: !84, inlinedAt: !223)
!225 = distinct !{!225, !198, !226}
!226 = !DILocation(line: 137, column: 2, scope: !190)
!227 = !DILocation(line: 124, column: 22, scope: !190)
!228 = !DILocation(line: 0, scope: !117, inlinedAt: !229)
!229 = distinct !DILocation(line: 138, column: 9, scope: !190)
!230 = !DILocation(line: 68, column: 13, scope: !117, inlinedAt: !229)
!231 = !DILocation(line: 69, column: 14, scope: !117, inlinedAt: !229)
!232 = !DILocation(line: 70, column: 20, scope: !117, inlinedAt: !229)
!233 = !DILocation(line: 71, column: 9, scope: !117, inlinedAt: !229)
!234 = !DILocation(line: 72, column: 1, scope: !117, inlinedAt: !229)
!235 = !DILocation(line: 139, column: 1, scope: !190)
!236 = distinct !DISubprogram(name: "tnum_intersect", scope: !3, file: !3, line: 144, type: !118, scopeLine: 145, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !237)
!237 = !{!238, !239, !240, !241}
!238 = !DILocalVariable(name: "a", arg: 1, scope: !236, file: !3, line: 144, type: !33)
!239 = !DILocalVariable(name: "b", arg: 2, scope: !236, file: !3, line: 144, type: !33)
!240 = !DILocalVariable(name: "v", scope: !236, file: !3, line: 146, type: !37)
!241 = !DILocalVariable(name: "mu", scope: !236, file: !3, line: 146, type: !37)
!242 = !DILocation(line: 0, scope: !236)
!243 = !DILocation(line: 148, column: 14, scope: !236)
!244 = !DILocation(line: 149, column: 14, scope: !236)
!245 = !DILocation(line: 150, column: 9, scope: !236)
!246 = !DILocation(line: 151, column: 1, scope: !236)
!247 = distinct !DISubprogram(name: "tnum_union", scope: !3, file: !3, line: 153, type: !118, scopeLine: 154, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !248)
!248 = !{!249, !250, !251, !252}
!249 = !DILocalVariable(name: "a", arg: 1, scope: !247, file: !3, line: 153, type: !33)
!250 = !DILocalVariable(name: "b", arg: 2, scope: !247, file: !3, line: 153, type: !33)
!251 = !DILocalVariable(name: "v", scope: !247, file: !3, line: 155, type: !37)
!252 = !DILocalVariable(name: "mu", scope: !247, file: !3, line: 155, type: !37)
!253 = !DILocation(line: 0, scope: !247)
!254 = !DILocation(line: 157, column: 14, scope: !247)
!255 = !DILocation(line: 158, column: 14, scope: !247)
!256 = !DILocation(line: 158, column: 34, scope: !247)
!257 = !DILocation(line: 158, column: 23, scope: !247)
!258 = !DILocation(line: 159, column: 9, scope: !247)
!259 = !DILocation(line: 160, column: 1, scope: !247)
!260 = distinct !DISubprogram(name: "tnum_shl", scope: !3, file: !3, line: 162, type: !261, scopeLine: 163, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !263)
!261 = !DISubroutineType(types: !262)
!262 = !{!33, !33, !33, !62}
!263 = !{!264, !265, !266, !267}
!264 = !DILocalVariable(name: "a", arg: 1, scope: !260, file: !3, line: 162, type: !33)
!265 = !DILocalVariable(name: "b", arg: 2, scope: !260, file: !3, line: 162, type: !33)
!266 = !DILocalVariable(name: "insn_bitness", arg: 3, scope: !260, file: !3, line: 162, type: !62)
!267 = !DILocalVariable(name: "amt", scope: !260, file: !3, line: 164, type: !62)
!268 = !DILocation(line: 0, scope: !260)
!269 = !DILocation(line: 166, column: 29, scope: !260)
!270 = !DILocation(line: 166, column: 42, scope: !260)
!271 = !DILocation(line: 0, scope: !155, inlinedAt: !272)
!272 = distinct !DILocation(line: 166, column: 6, scope: !260)
!273 = !DILocation(line: 90, column: 18, scope: !155, inlinedAt: !272)
!274 = !DILocation(line: 92, column: 14, scope: !155, inlinedAt: !272)
!275 = !DILocation(line: 93, column: 9, scope: !155, inlinedAt: !272)
!276 = !DILocation(line: 168, column: 17, scope: !260)
!277 = !DILocation(line: 168, column: 2, scope: !260)
!278 = !DILocation(line: 169, column: 14, scope: !279)
!279 = distinct !DILexicalBlock(scope: !280, file: !3, line: 169, column: 7)
!280 = distinct !DILexicalBlock(scope: !260, file: !3, line: 168, column: 28)
!281 = !DILocation(line: 0, scope: !280)
!282 = !DILocation(line: 169, column: 7, scope: !280)
!283 = !DILocation(line: 0, scope: !84, inlinedAt: !284)
!284 = distinct !DILocation(line: 170, column: 22, scope: !279)
!285 = !DILocation(line: 39, column: 9, scope: !84, inlinedAt: !284)
!286 = !DILocation(line: 0, scope: !247, inlinedAt: !287)
!287 = distinct !DILocation(line: 170, column: 8, scope: !279)
!288 = !DILocation(line: 157, column: 14, scope: !247, inlinedAt: !287)
!289 = !DILocation(line: 158, column: 14, scope: !247, inlinedAt: !287)
!290 = !DILocation(line: 158, column: 34, scope: !247, inlinedAt: !287)
!291 = !DILocation(line: 158, column: 23, scope: !247, inlinedAt: !287)
!292 = !DILocation(line: 159, column: 9, scope: !247, inlinedAt: !287)
!293 = !DILocation(line: 170, column: 4, scope: !279)
!294 = !DILocation(line: 172, column: 15, scope: !295)
!295 = distinct !DILexicalBlock(scope: !280, file: !3, line: 172, column: 7)
!296 = !DILocation(line: 172, column: 7, scope: !280)
!297 = !DILocation(line: 175, column: 7, scope: !280)
!298 = !DILocation(line: 0, scope: !93, inlinedAt: !299)
!299 = distinct !DILocation(line: 176, column: 7, scope: !280)
!300 = !DILocation(line: 44, column: 9, scope: !93, inlinedAt: !299)
!301 = distinct !{!301, !277, !302}
!302 = !DILocation(line: 177, column: 2, scope: !260)
!303 = !DILocation(line: 180, column: 1, scope: !260)
!304 = distinct !DISubprogram(name: "tnum_lshr", scope: !3, file: !3, line: 182, type: !261, scopeLine: 183, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !305)
!305 = !{!306, !307, !308, !309}
!306 = !DILocalVariable(name: "a", arg: 1, scope: !304, file: !3, line: 182, type: !33)
!307 = !DILocalVariable(name: "b", arg: 2, scope: !304, file: !3, line: 182, type: !33)
!308 = !DILocalVariable(name: "insn_bitness", arg: 3, scope: !304, file: !3, line: 182, type: !62)
!309 = !DILocalVariable(name: "amt", scope: !304, file: !3, line: 184, type: !62)
!310 = !DILocation(line: 0, scope: !304)
!311 = !DILocation(line: 186, column: 29, scope: !304)
!312 = !DILocation(line: 186, column: 42, scope: !304)
!313 = !DILocation(line: 0, scope: !155, inlinedAt: !314)
!314 = distinct !DILocation(line: 186, column: 6, scope: !304)
!315 = !DILocation(line: 90, column: 18, scope: !155, inlinedAt: !314)
!316 = !DILocation(line: 92, column: 14, scope: !155, inlinedAt: !314)
!317 = !DILocation(line: 93, column: 9, scope: !155, inlinedAt: !314)
!318 = !DILocation(line: 188, column: 17, scope: !304)
!319 = !DILocation(line: 188, column: 2, scope: !304)
!320 = !DILocation(line: 189, column: 14, scope: !321)
!321 = distinct !DILexicalBlock(scope: !322, file: !3, line: 189, column: 7)
!322 = distinct !DILexicalBlock(scope: !304, file: !3, line: 188, column: 28)
!323 = !DILocation(line: 0, scope: !322)
!324 = !DILocation(line: 189, column: 7, scope: !322)
!325 = !DILocation(line: 0, scope: !93, inlinedAt: !326)
!326 = distinct !DILocation(line: 190, column: 22, scope: !321)
!327 = !DILocation(line: 44, column: 9, scope: !93, inlinedAt: !326)
!328 = !DILocation(line: 0, scope: !247, inlinedAt: !329)
!329 = distinct !DILocation(line: 190, column: 8, scope: !321)
!330 = !DILocation(line: 157, column: 14, scope: !247, inlinedAt: !329)
!331 = !DILocation(line: 158, column: 14, scope: !247, inlinedAt: !329)
!332 = !DILocation(line: 158, column: 34, scope: !247, inlinedAt: !329)
!333 = !DILocation(line: 158, column: 23, scope: !247, inlinedAt: !329)
!334 = !DILocation(line: 159, column: 9, scope: !247, inlinedAt: !329)
!335 = !DILocation(line: 190, column: 4, scope: !321)
!336 = !DILocation(line: 192, column: 15, scope: !337)
!337 = distinct !DILexicalBlock(scope: !322, file: !3, line: 192, column: 7)
!338 = !DILocation(line: 192, column: 7, scope: !322)
!339 = !DILocation(line: 195, column: 7, scope: !322)
!340 = !DILocation(line: 0, scope: !93, inlinedAt: !341)
!341 = distinct !DILocation(line: 196, column: 7, scope: !322)
!342 = !DILocation(line: 44, column: 9, scope: !93, inlinedAt: !341)
!343 = distinct !{!343, !319, !344}
!344 = !DILocation(line: 197, column: 2, scope: !304)
!345 = !DILocation(line: 200, column: 1, scope: !304)
!346 = distinct !DISubprogram(name: "tnum_cast", scope: !3, file: !3, line: 202, type: !85, scopeLine: 203, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !347)
!347 = !{!348, !349}
!348 = !DILocalVariable(name: "a", arg: 1, scope: !346, file: !3, line: 202, type: !33)
!349 = !DILocalVariable(name: "size", arg: 2, scope: !346, file: !3, line: 202, type: !62)
!350 = !DILocation(line: 0, scope: !346)
!351 = !DILocation(line: 204, column: 23, scope: !346)
!352 = !DILocation(line: 204, column: 28, scope: !346)
!353 = !DILocation(line: 204, column: 34, scope: !346)
!354 = !DILocation(line: 204, column: 10, scope: !346)
!355 = !DILocation(line: 205, column: 9, scope: !346)
!356 = !DILocation(line: 206, column: 2, scope: !346)
!357 = distinct !DISubprogram(name: "tnum_is_aligned", scope: !3, file: !3, line: 209, type: !358, scopeLine: 210, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !362)
!358 = !DISubroutineType(types: !359)
!359 = !{!360, !33, !37}
!360 = !DIDerivedType(tag: DW_TAG_typedef, name: "bool", file: !23, line: 30, baseType: !361)
!361 = !DIBasicType(name: "_Bool", size: 8, encoding: DW_ATE_boolean)
!362 = !{!363, !364}
!363 = !DILocalVariable(name: "a", arg: 1, scope: !357, file: !3, line: 209, type: !33)
!364 = !DILocalVariable(name: "size", arg: 2, scope: !357, file: !3, line: 209, type: !37)
!365 = !DILocation(line: 0, scope: !357)
!366 = !DILocation(line: 211, column: 7, scope: !367)
!367 = distinct !DILexicalBlock(scope: !357, file: !3, line: 211, column: 6)
!368 = !DILocation(line: 211, column: 6, scope: !357)
!369 = !DILocation(line: 214, column: 1, scope: !357)
!370 = distinct !DISubprogram(name: "tnum_in", scope: !3, file: !3, line: 216, type: !371, scopeLine: 217, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !373)
!371 = !DISubroutineType(types: !372)
!372 = !{!360, !33, !33}
!373 = !{!374, !375}
!374 = !DILocalVariable(name: "a", arg: 1, scope: !370, file: !3, line: 216, type: !33)
!375 = !DILocalVariable(name: "b", arg: 2, scope: !370, file: !3, line: 216, type: !33)
!376 = !DILocation(line: 0, scope: !370)
!377 = !DILocation(line: 218, column: 15, scope: !378)
!378 = distinct !DILexicalBlock(scope: !370, file: !3, line: 218, column: 6)
!379 = !DILocation(line: 218, column: 13, scope: !378)
!380 = !DILocation(line: 218, column: 6, scope: !370)
!381 = !DILocation(line: 222, column: 1, scope: !370)
!382 = distinct !DISubprogram(name: "tnum_strn", scope: !3, file: !3, line: 224, type: !383, scopeLine: 225, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !387)
!383 = !DISubroutineType(types: !384)
!384 = !{!18, !385, !22, !33}
!385 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !386, size: 64)
!386 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!387 = !{!388, !389, !390}
!388 = !DILocalVariable(name: "str", arg: 1, scope: !382, file: !3, line: 224, type: !385)
!389 = !DILocalVariable(name: "size", arg: 2, scope: !382, file: !3, line: 224, type: !22)
!390 = !DILocalVariable(name: "a", arg: 3, scope: !382, file: !3, line: 224, type: !33)
!391 = !DILocation(line: 0, scope: !382)
!392 = !DILocation(line: 226, column: 9, scope: !382)
!393 = !DILocation(line: 226, column: 2, scope: !382)
!394 = distinct !DISubprogram(name: "tnum_sbin", scope: !3, file: !3, line: 230, type: !383, scopeLine: 231, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !395)
!395 = !{!396, !397, !398, !399, !400, !402}
!396 = !DILocalVariable(name: "str", arg: 1, scope: !394, file: !3, line: 230, type: !385)
!397 = !DILocalVariable(name: "size", arg: 2, scope: !394, file: !3, line: 230, type: !22)
!398 = !DILocalVariable(name: "a", arg: 3, scope: !394, file: !3, line: 230, type: !33)
!399 = !DILocalVariable(name: "n", scope: !394, file: !3, line: 232, type: !22)
!400 = !DILocalVariable(name: "__UNIQUE_ID___x2", scope: !401, file: !3, line: 246, type: !27)
!401 = distinct !DILexicalBlock(scope: !394, file: !3, line: 246, column: 6)
!402 = !DILocalVariable(name: "__UNIQUE_ID___y3", scope: !401, file: !3, line: 246, type: !22)
!403 = !DILocation(line: 0, scope: !394)
!404 = !DILocation(line: 234, column: 2, scope: !405)
!405 = distinct !DILexicalBlock(scope: !394, file: !3, line: 234, column: 2)
!406 = !DILocation(line: 235, column: 9, scope: !407)
!407 = distinct !DILexicalBlock(scope: !408, file: !3, line: 235, column: 7)
!408 = distinct !DILexicalBlock(scope: !409, file: !3, line: 234, column: 23)
!409 = distinct !DILexicalBlock(scope: !405, file: !3, line: 234, column: 2)
!410 = !DILocation(line: 235, column: 7, scope: !408)
!411 = !DILocation(line: 234, column: 19, scope: !409)
!412 = !DILocation(line: 236, column: 15, scope: !413)
!413 = distinct !DILexicalBlock(scope: !414, file: !3, line: 236, column: 8)
!414 = distinct !DILexicalBlock(scope: !407, file: !3, line: 235, column: 17)
!415 = !DILocation(line: 236, column: 8, scope: !414)
!416 = !DILocation(line: 237, column: 11, scope: !413)
!417 = !DILocation(line: 237, column: 5, scope: !413)
!418 = !DILocation(line: 237, column: 16, scope: !413)
!419 = !DILocation(line: 238, column: 21, scope: !420)
!420 = distinct !DILexicalBlock(scope: !413, file: !3, line: 238, column: 13)
!421 = !DILocation(line: 0, scope: !420)
!422 = !DILocation(line: 238, column: 13, scope: !413)
!423 = !DILocation(line: 239, column: 16, scope: !420)
!424 = !DILocation(line: 239, column: 5, scope: !420)
!425 = !DILocation(line: 241, column: 16, scope: !420)
!426 = !DILocation(line: 243, column: 10, scope: !408)
!427 = !DILocation(line: 244, column: 11, scope: !408)
!428 = distinct !{!428, !404, !429}
!429 = !DILocation(line: 245, column: 2, scope: !405)
!430 = !DILocation(line: 246, column: 6, scope: !401)
!431 = !DILocation(line: 0, scope: !401)
!432 = !DILocation(line: 246, column: 2, scope: !394)
!433 = !DILocation(line: 246, column: 33, scope: !394)
!434 = !DILocation(line: 247, column: 2, scope: !394)
!435 = distinct !DISubprogram(name: "tnum_subreg", scope: !3, file: !3, line: 250, type: !436, scopeLine: 251, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !438)
!436 = !DISubroutineType(types: !437)
!437 = !{!33, !33}
!438 = !{!439}
!439 = !DILocalVariable(name: "a", arg: 1, scope: !435, file: !3, line: 250, type: !33)
!440 = !DILocation(line: 0, scope: !435)
!441 = !DILocation(line: 0, scope: !346, inlinedAt: !442)
!442 = distinct !DILocation(line: 252, column: 9, scope: !435)
!443 = !DILocation(line: 204, column: 10, scope: !346, inlinedAt: !442)
!444 = !DILocation(line: 205, column: 9, scope: !346, inlinedAt: !442)
!445 = !DILocation(line: 206, column: 2, scope: !346, inlinedAt: !442)
!446 = !DILocation(line: 252, column: 2, scope: !435)
!447 = distinct !DISubprogram(name: "tnum_clear_subreg", scope: !3, file: !3, line: 255, type: !436, scopeLine: 256, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !448)
!448 = !{!449}
!449 = !DILocalVariable(name: "a", arg: 1, scope: !447, file: !3, line: 255, type: !33)
!450 = !DILocation(line: 0, scope: !447)
!451 = !DILocation(line: 39, column: 9, scope: !84, inlinedAt: !452)
!452 = distinct !DILocation(line: 257, column: 9, scope: !447)
!453 = !DILocation(line: 0, scope: !84, inlinedAt: !452)
!454 = !DILocation(line: 39, column: 2, scope: !84, inlinedAt: !452)
!455 = !DILocation(line: 257, column: 2, scope: !447)
!456 = distinct !DISubprogram(name: "tnum_const_subreg", scope: !3, file: !3, line: 260, type: !457, scopeLine: 261, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !459)
!457 = !DISubroutineType(types: !458)
!458 = !{!33, !33, !12}
!459 = !{!460, !461}
!460 = !DILocalVariable(name: "a", arg: 1, scope: !456, file: !3, line: 260, type: !33)
!461 = !DILocalVariable(name: "value", arg: 2, scope: !456, file: !3, line: 260, type: !12)
!462 = !DILocation(line: 0, scope: !456)
!463 = !DILocation(line: 0, scope: !447, inlinedAt: !464)
!464 = distinct !DILocation(line: 262, column: 17, scope: !456)
!465 = !DILocation(line: 39, column: 9, scope: !84, inlinedAt: !466)
!466 = distinct !DILocation(line: 257, column: 9, scope: !447, inlinedAt: !464)
!467 = !DILocation(line: 0, scope: !84, inlinedAt: !466)
!468 = !DILocation(line: 262, column: 50, scope: !456)
!469 = !DILocation(line: 0, scope: !168, inlinedAt: !470)
!470 = distinct !DILocation(line: 262, column: 9, scope: !456)
!471 = !DILocation(line: 100, column: 14, scope: !168, inlinedAt: !470)
!472 = !DILocation(line: 102, column: 9, scope: !168, inlinedAt: !470)
!473 = !DILocation(line: 103, column: 1, scope: !168, inlinedAt: !470)
!474 = !DILocation(line: 262, column: 2, scope: !456)
