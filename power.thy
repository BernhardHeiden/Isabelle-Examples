theory power 
  imports Main 
begin

  (*
    We define the property of power x^n. We will recursively go through till n is equal to 0.
  *)
  primrec pow :: "nat => nat => nat"
    where
      "pow x 0       = Suc 0"
    | "pow x (Suc n) = x * pow x n"
  
  
  
  (*
    We will prove that when we multiply the powers,
    its the same as doing the power twice first with m then with n.
  *)
  
  (*
    First we will prove the base case, which is multiplying the
    results of two powered numbers is the same as adding the powers before hand.
    We use induction tactic on the power and apply auto.
  *)
  lemma pow_add: "pow x (m + n) = pow x m * pow x n"
    apply (induct n)
    apply auto
  done
  
  (*
    This uses the base case that we proved above using the lemma.
    We use induction tactic on the power and apply auto.
  *)
  theorem pow_mult: "pow x (m * n) = pow (pow x m) n"
    apply (induct n)
    apply (auto simp add: pow_add)
  done

end