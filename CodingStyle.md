# Coding style

## File name

* Directory: `directory`
* Files: `File.*` || `FileName.*`

## Documentation

* `doxygen` for C
* `coqdoc` for coq
* Start each file with a comment with a module description

## `git`

* Linux rules: Verb + sentence + summry
* One commit per goal/contribution
* When we need to commit just for archiving purposes, we use a temporary
  `bob-tmp-num` branch. that branch will be merge back on `master` by a
  `git merge --squash` when the actual commit can be done, and the `tmp` branch
  deleted.

## Coding

### Coq:

* Function: `verbNoun` || `verbNounAux`
* Variable: `nounAdj`
* Parameter: `noun` || `nounNumber`
* Indentation: use the script `pepindent.hs`
* Lemma: use the same pattern used for function and use module for lemma of a
  specific function
* Proof: use only one level of bullet and only one dot per line

### C:

* Use `stdint.h`
* Indentation: `\t`
