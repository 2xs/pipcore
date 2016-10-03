
# coding style
## filename 
    * directory :  directory
    * files :  File.* || FileName.* 
    
## doc 
    * doxygen for C 
    * coqdoc for coq
    * Start each file with a comment with a module description

## git
     * linux rules : Verb + sentence + summry 
     * one commit per goal/contribution/ 
     * when we need to commit just for archiving purposes, we use a temporary bob-tmp-num branch.
       that branch will be merge back on master by a "git merge --squash" when the actual commit can be done, and the tmp branch deleted.

## coding
### Coq :
      * function : verbNoun || verbNounAux 
      * variable : nounAdj 
      * parameter : noun || nounNumber
      * indentation : use the script pepindent.hs 
      * lemma : use the same pattern used for function and use module for lemma of a specific function  
      * proof : use only one level of bullet and only one dot per line,  
     
### C :
      * use stdint.h  
      * indentation \t
