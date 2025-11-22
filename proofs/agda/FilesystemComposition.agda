{- Valence Shell - Filesystem Composition (Agda)

   Composition theorems for filesystem operations
-}

module FilesystemComposition where

open import FilesystemModel
open import FileOperations
open import Data.List using (List; []; _∷_; reverse; map; _++_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- Operation type
data Operation : Set where
  mkdirOp : Path → Operation
  rmdirOp : Path → Operation
  createFileOp : Path → Operation
  deleteFileOp : Path → Operation

-- Apply operation
applyOp : Operation → Filesystem → Filesystem
applyOp (mkdirOp p) fs = mkdir p fs
applyOp (rmdirOp p) fs = rmdir p fs
applyOp (createFileOp p) fs = createFile p fs
applyOp (deleteFileOp p) fs = deleteFile p fs

-- Reverse operation
reverseOp : Operation → Operation
reverseOp (mkdirOp p) = rmdirOp p
reverseOp (rmdirOp p) = mkdirOp p
reverseOp (createFileOp p) = createFileOp p
reverseOp (deleteFileOp p) = createFileOp p

-- Apply sequence
applySequence : List Operation → Filesystem → Filesystem
applySequence [] fs = fs
applySequence (op ∷ ops) fs = applySequence ops (applyOp op fs)

-- Reverse sequence
reverseSequence : List Operation → List Operation
reverseSequence ops = map reverseOp (reverse ops)

-- Precondition
opPrecondition : Operation → Filesystem → Set
opPrecondition (mkdirOp p) fs = MkdirPrecondition p fs
opPrecondition (rmdirOp p) fs = RmdirPrecondition p fs
opPrecondition (createFileOp p) fs = CreateFilePrecondition p fs
opPrecondition (deleteFileOp p) fs = DeleteFilePrecondition p fs

-- Reversible
record Reversible (op : Operation) (fs : Filesystem) : Set where
  field
    precondition : opPrecondition op fs
    reversePrecondition : opPrecondition (reverseOp op) (applyOp op fs)

-- All reversible
data AllReversible : List Operation → Filesystem → Set where
  nilReversible : ∀ {fs} → AllReversible [] fs
  consReversible : ∀ {op ops fs} →
    Reversible op fs →
    AllReversible ops (applyOp op fs) →
    AllReversible (op ∷ ops) fs

-- Single operation reversibility
singleOpReversible : ∀ (op : Operation) (fs : Filesystem) →
  Reversible op fs →
  applyOp (reverseOp op) (applyOp op fs) ≡ fs
singleOpReversible (mkdirOp p) fs rev = mkdir-rmdir-reversible p fs (Reversible.precondition rev)
singleOpReversible (rmdirOp p) fs rev = {!!} -- Would need rmdir-mkdir proof
singleOpReversible (createFileOp p) fs rev = createFile-deleteFile-reversible p fs (Reversible.precondition rev)
singleOpReversible (deleteFileOp p) fs rev = {!!}

-- Main composition theorem (statement)
postulate
  operationSequenceReversible : ∀ (ops : List Operation) (fs : Filesystem) →
    AllReversible ops fs →
    applySequence (reverseSequence ops) (applySequence ops fs) ≡ fs
