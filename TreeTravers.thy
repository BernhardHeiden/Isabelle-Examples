theory TreeTravers 
  imports Main 
begin

  (*
    We define a new data type `'a tree` which is for binary tree, 
    where both leafs and nodes have a value
  *)
  datatype 'a tree = 
    Tip "'a" 
    | Node "'a" "'a tree" "'a tree"



  (*
    We define a property called preOrder which takes a tree and
    returns a list with the value at the start. 
  *)
  primrec preOrder :: "'a tree \<Rightarrow> 'a list"
    where
      "preOrder (Tip a)      = [a]"
    | "preOrder (Node f x y) = f#((preOrder x)@(preOrder y))"
  
  (*
    We define a property called postOrder which takes a tree and
    returns a list with the value at the end. 
  *)
  primrec postOrder :: "'a tree \<Rightarrow> 'a list"
    where
      "postOrder (Tip a)      = [a]"
    | "postOrder (Node f x y) = (postOrder x)@(postOrder y)@[f]"
  
  (*
    We define a property called inOrder which takes a tree and
    returns a list with the value at the in location. 
  *)
  primrec inOrder :: "'a tree \<Rightarrow> 'a list"
    where
      "inOrder (Tip a)      = [a]"
    | "inOrder (Node f x y) = (inOrder x)@[f]@(inOrder y)"

  (*
    We define a property called mirror which takes a tree and
    returns a tree with ever left leaf swapped with the right leaf. 
  *)
  primrec mirror :: "'a tree \<Rightarrow> 'a tree"
    where
      "mirror (Tip a)      = (Tip a)"
    | "mirror (Node f x y) = (Node f (mirror y) (mirror x))"



  (*
    Now we will prove that by converting a tree in to a list and then reversing it is the same as
    mirroing a tree and then converting it into a list. 
  *)

  (*
    We will do it for preOrder, we will apply induction tactic on the tree using auto
  *)
  theorem  "preOrder (mirror t) = rev (postOrder t)"
    apply (induct_tac t)
    apply auto
  done
  
  (*
    We will do it for postOrder, we will apply induction tactic on the tree using auto
  *)
  theorem "postOrder (mirror t) = rev (preOrder t)"
    apply (induct_tac t)
    apply auto
  done
  
  (*
    We will do it for inOrder, we will apply induction tactic on the tree using auto
  *)
  theorem "inOrder (mirror t) = rev (inOrder t)"
    apply (induct_tac t)
    apply auto
  done

end