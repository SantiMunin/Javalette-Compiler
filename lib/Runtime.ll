@dnl = internal constant [4 x i8] c"%d\0A\00"
@fnl = internal constant [6 x i8] c"%.1f\0A\00"
@d   = internal constant [3 x i8] c"%d\00"	
@lf  = internal constant [4 x i8] c"%lf\00"	

declare i32 @printf(i8*, ...) 
declare i32 @scanf(i8*, ...)
declare i32 @puts(i8*)
declare void @exit(i32)

define void @printInt(i32 %x) {
entry: %t0 = getelementptr [4 x i8]* @dnl, i32 0, i32 0
       call i32 (i8*, ...)* @printf(i8* %t0, i32 %x) 
       ret void
}

define void @printDouble(double %x) {
entry: %t0 = getelementptr [6 x i8]* @fnl, i32 0, i32 0
       call i32 (i8*, ...)* @printf(i8* %t0, double %x) 
       ret void
}

define void @printString(i8* %s) {
entry:  call i32 @puts(i8* %s)
	ret void
}

define i32 @readInt() {
entry: %res = alloca i32
        %t1 = getelementptr [3 x i8]* @d, i32 0, i32 0
	call i32 (i8*, ...)* @scanf(i8* %t1, i32* %res)
	%t2 = load i32* %res
	ret i32 %t2
}

define double @readDouble() {
entry: %res = alloca double
        %t1 = getelementptr [4 x i8]* @lf, i32 0, i32 0
	call i32 (i8*, ...)* @scanf(i8* %t1, double* %res)
	%t2 = load double* %res
	ret double %t2
}


;; Dynamic distpatch

%ClassMethod = type { i64, %ClassMethod*, i8* }
%ClassDescriptor = type { %ClassDescriptor*, %ClassMethod* }

; Function Attrs: nounwind ssp uwtable
define i8* @search_method(%ClassMethod* %entry, i64 %tag) #0 {
  %1 = alloca i8*, align 8
  %2 = alloca %ClassMethod*, align 8
  %3 = alloca i64, align 8
  store %ClassMethod* %entry, %ClassMethod** %2, align 8
  store i64 %tag, i64* %3, align 8
  %4 = load %ClassMethod** %2, align 8
  %5 = icmp eq %ClassMethod* %4, null
  br i1 %5, label %6, label %7

; <label>:6                                       ; preds = %0
  store i8* null, i8** %1
  br label %23

; <label>:7                                       ; preds = %0
  %8 = load %ClassMethod** %2, align 8
  %9 = getelementptr inbounds %ClassMethod* %8, i32 0, i32 0
  %10 = load i64* %9, align 8
  %11 = load i64* %3, align 8
  %12 = icmp eq i64 %10, %11
  br i1 %12, label %13, label %17

; <label>:13                                      ; preds = %7
  %14 = load %ClassMethod** %2, align 8
  %15 = getelementptr inbounds %ClassMethod* %14, i32 0, i32 2
  %16 = load i8** %15, align 8
  store i8* %16, i8** %1
  br label %23

; <label>:17                                      ; preds = %7
  %18 = load %ClassMethod** %2, align 8
  %19 = getelementptr inbounds %ClassMethod* %18, i32 0, i32 1
  %20 = load %ClassMethod** %19, align 8
  %21 = load i64* %3, align 8
  %22 = call i8* @search_method(%ClassMethod* %20, i64 %21)
  store i8* %22, i8** %1
  br label %23

; <label>:23                                      ; preds = %17, %13, %6
  %24 = load i8** %1
  ret i8* %24
}

; Function Attrs: nounwind ssp uwtable
define i8* @dispatcher(i64 %tag, %ClassDescriptor* %descr) #0 {
  %1 = alloca i8*, align 8
  %2 = alloca i64, align 8
  %3 = alloca %ClassDescriptor*, align 8
  %entry = alloca i8*, align 8
  store i64 %tag, i64* %2, align 8
  store %ClassDescriptor* %descr, %ClassDescriptor** %3, align 8
  %4 = load %ClassDescriptor** %3, align 8
  %5 = getelementptr inbounds %ClassDescriptor* %4, i32 0, i32 1
  %6 = load %ClassMethod** %5, align 8
  %7 = load i64* %2, align 8
  %8 = call i8* @search_method(%ClassMethod* %6, i64 %7)
  store i8* %8, i8** %entry, align 8
  %9 = load %ClassDescriptor** %3, align 8
  %10 = icmp eq %ClassDescriptor* %9, null
  br i1 %10, label %11, label %15

; <label>:11                                      ; preds = %0
  %12 = load i8** %entry, align 8
  %13 = icmp eq i8* %12, null
  br i1 %13, label %14, label %15

; <label>:14                                      ; preds = %11
  call void @exit(i32 1)
  unreachable

; <label>:15                                      ; preds = %11, %0
  %16 = load i8** %entry, align 8
  %17 = icmp eq i8* %16, null
  br i1 %17, label %18, label %24

; <label>:18                                      ; preds = %15
  %19 = load i64* %2, align 8
  %20 = load %ClassDescriptor** %3, align 8
  %21 = getelementptr inbounds %ClassDescriptor* %20, i32 0, i32 0
  %22 = load %ClassDescriptor** %21, align 8
  %23 = call i8* @dispatcher(i64 %19, %ClassDescriptor* %22)
  store i8* %23, i8** %1
  br label %26

; <label>:24                                      ; preds = %15
  %25 = load i8** %entry, align 8
  store i8* %25, i8** %1
  br label %26

; <label>:26                                      ; preds = %24, %18
  %27 = load i8** %1
  ret i8* %27
}