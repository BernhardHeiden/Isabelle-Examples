(*
  Define file name and import all the stuff from main isabelle

  NOTE: We will be working with natural numbers so we will use 'nat'
*)
theory MergeSort
  imports Main

begin

  (*
    In merge sort we have a function which splits a list into many sub lists and sorts them,
    we also have a function which merges 2 sub lists after they have been sorted.
  *)
  
  (*
    Function merge takes in two lists and puts them together
    If one of the list is empty we just return the non-empty list
    Other wise we go through each element of both list and compare the values and add them
    to the new list respectively.
  *)
  fun merge :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list"
    where
      "merge [] ys = ys"
    | "merge xs [] = xs"
    | "merge (x # xs) (y # ys) = (
                                   if x \<le> y then 
                                     x # merge xs (y # ys)
                                   else
                                     y # merge (x # xs) ys
                                 )"
  
  (*
    Function sort takes a list and returns a sorted list
    If the list is empty we return the an empty list.
    If the list has one element then it will return that one element in a list.
    Other wise we will get the mid of the list and recursively call sort and merge with the
    top half of the list and the bottom half of the list.
  *)
  fun sort :: "nat list \<Rightarrow> nat list"
    where
      "sort [] = []"
    | "sort [x] = [x]"
    | "sort xs = (
                   let mid = length xs div 2 in
                   merge (sort (take mid xs)) (sort (drop mid xs))
                 )"



  (*
    We will now define a few properties for sorting that need to be true.
  *)

  (*
    We define a property called 'less' which checks if the first element is
    less than all the elements in the list recursively
  *)
  primrec less :: "nat \<Rightarrow> nat list \<Rightarrow> bool"
    where
      "less value []     = True"
    | "less value (x#xs) = (value <= x & less value xs)"
  
  
  (*
    We define a property called 'sorted' which calls 'less' to check the value against every other
    value in the list. This ensures that our list is sorted. This is done recursively by calling
    sorted on every sublist.
  *)
  primrec sorted :: "nat list \<Rightarrow> bool"
    where
      "sorted []     = True"
    | "sorted (x#xs) = (less x xs & sorted xs)"



  (*
    We will now prove that our sort function is actually sorting our list.
    We will use our property called sorted which returns a boolean.
    We will start off by defining some of our base cases, we will apply simp to each of the lemma's
    so we can use them in our theorem.
  *)

  (*
    We need to insure that our x value is less than or equal to our y value
    We will use the built in induction tactic which we will apply to our list using auto.
  *)
  lemma compare_values [simp]: "x \<le> y \<Longrightarrow> less y xs \<longrightarrow> less x xs"
    apply (induct_tac xs)
    apply auto
  done
  
  (*
    We need to insure that the x value is less than all the values in the two lists separately and
    if they are merged.
    We will use the built in induction on both lists with induction on merge as well.
  *)
  lemma less_merge [simp]: "less x (merge xs ys) = (less x xs \<and> less x ys)"
    apply (induct xs ys rule: merge.induct)
    apply auto
  done
  
  (*
    We need to insure that the merged list is sorted and its equal to the two
    lists sorted separately.
    We will use the built in induction on both lists with induction on merge as well.
  *)
  lemma sorted_merge [simp]: "sorted (merge xs ys) = (sorted xs \<and> sorted ys)"
    apply(induct xs ys rule: merge.induct)
    apply (auto simp add: linorder_not_le order_less_le)
  done
  
  (*
    Using the bases cases (lemma's) we can now prove that our function sort actually sorts the list
    using our sorted property.
    We will use the built in induction tactic on the list and apply the induction rule on sort. 
  *)
  theorem "sorted(sort xs)"
    apply (induct_tac xs rule: sort.induct) 
    apply auto
  done

end