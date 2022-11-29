Module Type TypesModel.

  Parameter index : Type.
  Parameter index_d : index.
  Parameter page  : Type.
  Parameter page_d : page.
  Parameter paddr : Type.
  Parameter vaddr : Type.
  Parameter level : Type.
  Parameter level_d : level.
  Parameter count : Type.
  Parameter count_d : count.
  Parameter boolvaddr : Type.
  Parameter userValue : Type.
  Parameter contextAddr : Type.
  Parameter interruptMask : Type.
  Parameter int_mask_d : interruptMask.

  Inductive yield_checks : Type :=
| FAIL_INVALID_INT_LEVEL
| FAIL_INVALID_CTX_SAVE_INDEX
| FAIL_CALLER_CONTEXT_SAVE
| FAIL_UNAVAILABLE_TARGET_VIDT
| FAIL_UNAVAILABLE_TARGET_CTX
| FAIL_UNAVAILABLE_CALLER_VIDT
| FAIL_ROOT_CALLER
| FAIL_INVALID_CHILD
| FAIL_MASKED_INTERRUPT
| SUCCESS.

End TypesModel.