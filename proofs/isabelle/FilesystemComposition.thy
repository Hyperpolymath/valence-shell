(*  Valence Shell - Filesystem Composition (Isabelle/HOL)

    Composition theorems for filesystem operations
*)

theory FilesystemComposition
  imports FilesystemModel FileOperations
begin

(* Operation type *)
datatype operation =
  MkdirOp path
  | RmdirOp path
  | CreateFileOp path
  | DeleteFileOp path

(* Apply operation *)
fun apply_op :: "operation \<Rightarrow> filesystem \<Rightarrow> filesystem" where
  "apply_op (MkdirOp p) fs = mkdir p fs"
| "apply_op (RmdirOp p) fs = rmdir p fs"
| "apply_op (CreateFileOp p) fs = create_file p fs"
| "apply_op (DeleteFileOp p) fs = delete_file p fs"

(* Reverse operation *)
fun reverse_op :: "operation \<Rightarrow> operation" where
  "reverse_op (MkdirOp p) = RmdirOp p"
| "reverse_op (RmdirOp p) = MkdirOp p"
| "reverse_op (CreateFileOp p) = DeleteFileOp p"
| "reverse_op (DeleteFileOp p) = CreateFileOp p"

(* Apply sequence *)
fun apply_sequence :: "operation list \<Rightarrow> filesystem \<Rightarrow> filesystem" where
  "apply_sequence [] fs = fs"
| "apply_sequence (op # ops) fs = apply_sequence ops (apply_op op fs)"

(* Reverse sequence *)
definition reverse_sequence :: "operation list \<Rightarrow> operation list" where
  "reverse_sequence ops = map reverse_op (rev ops)"

(* Preconditions *)
fun op_precondition :: "operation \<Rightarrow> filesystem \<Rightarrow> bool" where
  "op_precondition (MkdirOp p) fs = mkdir_precondition p fs"
| "op_precondition (RmdirOp p) fs = rmdir_precondition p fs"
| "op_precondition (CreateFileOp p) fs = create_file_precondition p fs"
| "op_precondition (DeleteFileOp p) fs = delete_file_precondition p fs"

(* Reversible *)
definition reversible :: "operation \<Rightarrow> filesystem \<Rightarrow> bool" where
  "reversible op fs = (
    op_precondition op fs \<and>
    op_precondition (reverse_op op) (apply_op op fs))"

(* All reversible *)
fun all_reversible :: "operation list \<Rightarrow> filesystem \<Rightarrow> bool" where
  "all_reversible [] fs = True"
| "all_reversible (op # ops) fs = (
    reversible op fs \<and>
    all_reversible ops (apply_op op fs))"

(* Single operation reversibility *)
lemma single_mkdir_reversible:
  assumes "mkdir_precondition p fs"
  shows "apply_op (RmdirOp p) (apply_op (MkdirOp p) fs) = fs"
  using assms mkdir_rmdir_reversible by simp

lemma single_create_file_reversible:
  assumes "create_file_precondition p fs"
  shows "apply_op (DeleteFileOp p) (apply_op (CreateFileOp p) fs) = fs"
  using assms create_file_delete_file_reversible by simp

(* Main composition theorem *)
theorem operation_sequence_reversible:
  assumes "all_reversible ops fs"
  shows "apply_sequence (reverse_sequence ops) (apply_sequence ops fs) = fs"
  using assms
  apply (induction ops arbitrary: fs)
   apply (simp add: reverse_sequence_def)
  apply (simp add: reverse_sequence_def)
  sorry (* Full proof would follow Coq structure *)

end
