import GradMath.Basic.Basic
import Mathlib.Data.List.Sort

namespace LIST

universe u_1
variable {α:Type u_1}

lemma pairwiseImpliesForallTwo {R:α->α->Prop} {l:List α}{i j:Nat} (hl:l.Pairwise R)
(hi:i<l.length) (hj:j<l.length) (hij:i<j):R l[i] l[j] := by
  match l with
  |[] => 
    simp at hi
  |a1::l' => 
    simp at hl
    match j with
    |0 =>
      simp at hij
    |.succ j' =>
      rw [List.length_cons] at hj; 
      replace hj:=Nat.lt_of_succ_lt_succ hj
      have p1: (a1 :: l')[Nat.succ j'] = l'[j'] := by simp
      rw [p1]
      match i with
      |0 =>
        exact hl.left l'[j'] (listGetIsMem hj)
      |.succ n' =>
        rw [List.length_cons] at hi;
        replace hi:=Nat.lt_of_succ_lt_succ hi
        have p2: (a1 :: l')[Nat.succ n'] = l'[n'] := by simp
        rw [p2]; 
        exact pairwiseImpliesForallTwo hl.right hi hj (Nat.lt_of_succ_lt_succ hij)

lemma sortFirstIsMax (R:α → α → Prop)[DecidableRel R][IsTotal α R][IsTrans α R]
(l:List α)(h:0<l.length)(h':0<(l.mergeSort R).length:=l.length_mergeSort R ▸ h):
∀{x:α}, x∈l.mergeSort R -> x≠ (l.mergeSort R)[0] -> R (l.mergeSort R)[0] x :=by
  intro x hx1 hx2
  refine' Exists.elim (listMemIff.mp hx1) _
  intro j hj
  refine' Exists.elim hj _
  intro hj p1
  rw [p1.symm]
  have p2: 0< j := by
    by_contra hc
    simp at hc
    simp_rw [hc] at p1
    rw [p1.symm] at hx2; simp at hx2
  exact pairwiseImpliesForallTwo (l.sorted_mergeSort R) h' hj p2

lemma memSortIffMemOrig (R:α → α → Prop) [DecidableRel R] (l:List α) {x:α}  :
x∈l.mergeSort R ↔ x∈l := 
List.Perm.mem_iff (List.perm_mergeSort _ _)

 















