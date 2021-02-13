$"??_C@_0CA@LJBHNMO@Cursor?5of?5size?5?$CFlli?5with?5data?3?6?$AA@" = comdat any
$"??_C@_01EEMJAFIK@?6?$AA@" = comdat any
$"??_C@_03JLNFKLOC@?$CFi?5?$AA@" = comdat any

@"??_C@_0CA@LJBHNMO@Cursor?5of?5size?5?$CFlli?5with?5data?3?6?$AA@" = linkonce_odr dso_local unnamed_addr constant [32 x i8] c"Cursor of size %lli with data:\0A\00", comdat, align 1
@"??_C@_01EEMJAFIK@?6?$AA@" = linkonce_odr dso_local unnamed_addr constant [2 x i8] c"\0A\00", comdat, align 1
@"??_C@_03JLNFKLOC@?$CFi?5?$AA@" = linkonce_odr dso_local unnamed_addr constant [4 x i8] c"%i \00", comdat, align 1

$printf = comdat any
declare external ccc i32  @printf(i8*, ...)
declare external ccc i8*  @malloc(i64)
declare external ccc void @free(i8*)

%SizeIndices = type { i64, %SizeIndices* }
%Cursor = type { i64, i8*, %SizeIndices* }

define external ccc %Cursor @helium_new_cursor() {
0:
  %cursor1 = insertvalue %Cursor undef, i64 0, 0
  %data = tail call noalias dereferenceable_or_null(262144) i8* @malloc(i64 262144)
  %cursor2 = insertvalue %Cursor %cursor1, i8* %data, 1
  ret %Cursor %cursor2
}

define external ccc void @helium_memdump_cursor(%Cursor %0) {
  ;%2 = getelementptr inbounds %Cursor, %Cursor* %0, i64 0, i32 0
  ;%3 = load i64, i64* %2, align 8, !tbaa !19
  %2 = select i1 1, %Cursor %0, %Cursor %0
  %3 = extractvalue %Cursor %0, 0
  %4 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([32 x i8], [32 x i8]* @"??_C@_0CA@LJBHNMO@Cursor?5of?5size?5?$CFlli?5with?5data?3?6?$AA@", i64 0, i64 0), i64 %3)
  ;%5 = load i64, i64* %2, align 8, !tbaa !19
  %5 = extractvalue %Cursor %0, 0
  %6 = icmp sgt i64 %5, 0
  br i1 %6, label %7, label %9

7:                                                ; preds = %1
  ;%8 = getelementptr inbounds %Cursor, %Cursor* %0, i64 0, i32 1
  %8 = extractvalue %Cursor %0, 1
  br label %11

9:                                                ; preds = %11, %1
  %10 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @"??_C@_01EEMJAFIK@?6?$AA@", i64 0, i64 0))
  ret void

11:                                               ; preds = %7, %11
  %12 = phi i64 [ 0, %7 ], [ %18, %11 ]
  ;%13 = load i8*, i8** %8, align 8, !tbaa !21
  %13 = bitcast i8* %8 to i8*
  %14 = getelementptr inbounds i8, i8* %13, i64 %12
  %15 = load i8, i8* %14
  %16 = sext i8 %15 to i32
  %17 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @"??_C@_03JLNFKLOC@?$CFi?5?$AA@", i64 0, i64 0), i32 %16)
  %18 = add nuw nsw i64 %12, 1
  ;%19 = load i64, i64* %2, align 8, !tbaa !19
  %19 = select i1 1, i64 %3, i64 %3
  %20 = icmp slt i64 %18, %19
  br i1 %20, label %11, label %9
}

define external ccc %Cursor @helium_write_cursor_at(%Cursor %cursor, i64 %size, i64 %at, i8* %data) {
entry:
  ; I hope the cursor argument automatically gets shallowly copied from the callsite...
  br label %forStart
forStart:
  %counter = phi i64 [ 0, %entry ], [ %newCounter, %forBody ]
  %isForDone = icmp sge i64 %counter, %size
  br i1 %isForDone, label %exit, label %forBody
forBody:
  %writeIndex = add nuw nsw i64 %counter, %at
  %toWritePtr = getelementptr i8, i8* %data, i64 %counter
  %toWrite = load i8, i8* %toWritePtr
  ;%dest = extractvalue %Cursor %cursor, i64 1, i64 %writeIndex
  ;store i8 %toWrite, i8* %dest
  %destPtr = extractvalue %Cursor %cursor, 1
  %dest = getelementptr i8, i8* %destPtr, i64 %writeIndex
  store i8 %toWrite, i8* %dest
  %newCounter = add nuw nsw i64 %counter, 1
  br label %forStart
exit:
  ret %Cursor %cursor
}

define external ccc %Cursor @helium_write_cursor(%Cursor  %cursor, i64 %size, i8* %data) {
0:
  ; memdump the old cursor, do the actual writing
  call ccc void @helium_memdump_cursor(%Cursor %cursor)
  ;%currIndexPtr = getelementptr %Cursor, %Cursor %cursor, i64 0
  ;%currIndex = load i64, i64* %currIndexPtr
  %currIndex = extractvalue %Cursor %cursor, 0
  %newCursor = call ccc %Cursor @helium_write_cursor_at(%Cursor %cursor, i64 %size, i64 %currIndex, i8* %data)

  ; Write the new size to the cursor, memdump it again
  ;%newIndexPtr = getelementptr %Cursor, %Cursor %newCursor, i64 0
  ;%newCIndex = load i64, i64* %newIndexPtr
  ;store i64 %newIndex, i64* %newIndexPtr
  %newCIndex = extractvalue %Cursor %newCursor, 0
  %newIndex = add nuw nsw i64 %newCIndex, %size
  %resCursor = insertvalue %Cursor %newCursor, i64 %newIndex, 0

  ; return the new cursor
  call ccc void @helium_memdump_cursor(%Cursor %resCursor)
  ret %Cursor %resCursor
}

; TODO Zet hier comments bij
define external %Cursor @helium_reserve_cursor_sizes(%Cursor %cursor, i64 %sizes) {
entry:
  %buffer = alloca %SizeIndices
  %sizePlaceholder64 = alloca i64
  store i64 0, i64* %sizePlaceholder64
  %sizePlaceholder = bitcast i64* %sizePlaceholder64 to i8*
  br label %firstLoopStart

firstLoopStart:
  ; The fl prefix mean "first loop"
  ; for (int flCounter = 0; flCounter < sizes; ++flCounter)
  %flCounter = phi i64           [ 0,       %entry ], [ %flNewCounter, %firstLoopBody ]
  %flCursor  = phi %Cursor       [ %cursor, %entry ], [ %newCursor,    %firstLoopBody ]
  %flBuffer  = phi %SizeIndices* [ %buffer, %entry ], [ %newIndexPtr,  %firstLoopBody ]

  %enterFirstLoop = icmp sgt i64 %sizes, %flCounter
  br i1 %enterFirstLoop, label %firstLoopBody, label %firstLoopEnd

firstLoopBody:
  ; new SizeIndices()
  %newIndexVoidPtr = tail call ccc noalias dereferenceable_or_null(16) i8* @malloc(i64 16)
  %newIndexPtr = bitcast i8* %newIndexVoidPtr to %SizeIndices*

  ; new_size_indices->index = cursor.current_index
  %newIndexIndexPtr = getelementptr %SizeIndices, %SizeIndices* %newIndexPtr, i64 0, i32 0
  %cursorIndex = extractvalue %Cursor %flCursor, 0
  store i64 %cursorIndex, i64* %newIndexIndexPtr

  ; new_size_indices->next_element = buffer
  %newIndexNextPtr = getelementptr %SizeIndices, %SizeIndices* %newIndexPtr, i64 0, i32 1
  store %SizeIndices* %flBuffer, %SizeIndices** %newIndexNextPtr
  call ccc void @helium_memdump_cursor(%Cursor %flCursor)

  ; helium_write_cursor(cursor, 8, &0)
  %newCursor = call ccc %Cursor @helium_write_cursor(%Cursor %flCursor, i64 8, i8* %sizePlaceholder)

  ; Add one to counter so we loop finitely
  %flNewCounter = add nuw nsw i64 %flCounter, 1
  br label %firstLoopStart

firstLoopEnd:
  br label %secondLoopStart

secondLoopStart:
  %slCounter = phi i64           [ 0,         %firstLoopEnd ], [ %slNewCounter, %sndLoopBody ]
  %slCursor  = phi %Cursor       [ %flCursor, %firstLoopEnd ], [ %slNewCursor,  %sndLoopBody ]
  %slIndices = phi %SizeIndices* [ %flBuffer, %firstLoopEnd ], [ %temp,         %sndLoopBody ]
  
  ; for (int i = 0; i < size_count; ++i)
  %enterSecondLoop = icmp sgt i64 %sizes, %slCounter
  br i1 %enterSecondLoop, label %sndLoopBody, label %exit

; Slightly shorter name so that a few other lines are shorter
sndLoopBody:
  ; temp = buffer->next_element
  %tempPtr = getelementptr %SizeIndices, %SizeIndices* %slIndices, i64 0, i32 1
  %temp = load %SizeIndices*, %SizeIndices** %tempPtr

  ; buffer->next_element = cursor.size_indices
  %cursor_indices = extractvalue %Cursor %slCursor, 2
  store %SizeIndices* %cursor_indices, %SizeIndices** %tempPtr

  ; cursor.size_indices = buffer
  %slNewCursor = insertvalue %Cursor %slCursor, %SizeIndices* %slIndices, 2

  ; buffer = temp -- in the phi node
  ; Doing the ++i here
  %slNewCounter = add nuw nsw i64 %slCounter, 1
  br label %secondLoopStart

exit:
  ret %Cursor %slCursor
}

define external ccc %Cursor @helium_write_cursor_size(%Cursor %oldCursor, %Cursor %newCursor) {
entry:
  ; size = newCursor.current_index - oldCursor.currentIndex
  %oldIndex = extractvalue %Cursor %oldCursor, 0
  %newIndex = extractvalue %Cursor %newCursor, 0
  %size = sub nuw nsw i64 %newIndex, %oldIndex

  ; sizeIndex = newCursor.size_indices->index
  %sizeIndexStruct = extractvalue %Cursor %newCursor, 2
  %sizeIndexPtr = getelementptr %SizeIndices, %SizeIndices* %sizeIndexStruct, i64 0, i32 0
  %sizeIndex = load i64, i64* %sizeIndexPtr

  ; next = newCursor.size_indices->next_element
  %nextPtr = getelementptr %SizeIndices, %SizeIndices* %sizeIndexStruct, i64 0, i32 1
  %next = load %SizeIndices*, %SizeIndices** %nextPtr

  ; free(newCursor.size_indices)
  %sizeIndexStructVoid = bitcast %SizeIndices* %sizeIndexStruct to i8*
  call ccc void @free(i8* %sizeIndexStructVoid)

  ; newCursor.size_indices = next; (and call it updatedCursor, because LLVM)
  %updatedCursor = insertvalue %Cursor %newCursor, %SizeIndices* %next, 2

  ; retCursor = helium_write_cursor_at(updatedCursor, sizeof(size), size_index, &size)
  %size64 = alloca i64
  store i64 %size, i64* %size64
  %sizePtr = bitcast i64* %size64 to i8*
  %retCursor = call ccc %Cursor @helium_write_cursor_at(%Cursor %updatedCursor, i64 8, i64 %sizeIndex, i8* %sizePtr)

  ret %Cursor %retCursor
}

define external ccc i8* @helium_finish_cursor(%Cursor %cursor) {
  call ccc void @helium_memdump_cursor(%Cursor %cursor)

  %retval = extractvalue %Cursor %cursor, 1
  ret i8* %retval
}

