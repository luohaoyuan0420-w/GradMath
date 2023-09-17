import GradMath.Basic.Basic
import Mathlib.Algebra.BigOperators.Basic

namespace FinsetSumAndProd

universe u_1 u_2 u_3

variable {β:Type u_1} {α : Type u_2} {ι: Type u_3}
open FINSET SET

lemma listRangeSumEqFinsetRangeSum  [AddCommMonoid α] {f:ℕ->α} {n:ℕ}:
((List.range n).map f).sum = (Finset.range n).sum f := by
  match n with
  | 0 => simp
  | .succ n' =>
    simp [List.range_succ,Finset.range_succ]; 
    rw [@listRangeSumEqFinsetRangeSum _ f n']; 
    abel
    
lemma listRangeProdEqFinsetRangeProd  [CommMonoid α] {f:ℕ->α} {n:ℕ}:
((List.range n).map f).prod = (Finset.range n).prod f := by
  match n with
  | 0 => simp
  | .succ n' =>
    simp [List.range_succ,Finset.range_succ]; 
    rw [@listRangeProdEqFinsetRangeProd _ f n']; 
    rw [mul_comm]

lemma finsetDisjointUnionSum [AddCommMonoid α] [DecidableEq ι] {s1 s2:Finset ι} {f:ι->α}
(h:s1∩s2 = ∅ ):(s1∪s2).sum f = s1.sum f + s2.sum f := by
  have p1: Disjoint s1 s2 := by
    rw [Finset.disjoint_left]
    intro a ha; by_contra hc
    have p2:=finsetInterMemIff.mpr ⟨ha,hc ⟩ 
    rw [h] at p2; simp at p2
  exact Finset.sum_union p1

lemma finsetDisjointUnionProd [CommMonoid α] [DecidableEq ι] {s1 s2:Finset ι} {f:ι->α}
(h:s1∩s2 = ∅ ):(s1∪s2).prod f = s1.prod f * s2.prod f := by
  have p1: Disjoint s1 s2 := by
    rw [Finset.disjoint_left]
    intro a ha; by_contra hc
    have p2:=finsetInterMemIff.mpr ⟨ha,hc ⟩ 
    rw [h] at p2; simp at p2
  exact Finset.prod_union p1

/-
lemma finsetAbsSumLeSumAbs [AddCommMonoid α][DecidableEq ι][Preorder β][AddCommMonoid β] 
{s:Finset ι} {f:ι->α} {ρ:α->β} (h1:∀{a1 a1:α},(ρ (a1+a2)) ≤ (ρ a1)+(ρ a2) ) (h2:ρ 0 =0):
ρ (s.sum f) ≤ s.sum (fun x =>ρ (f x)) := by 
  let rec aux {s':Finset ι} {n:ℕ} (h:s'.card = n):
  ρ (s'.sum f) ≤ s'.sum (fun x =>ρ (f x)) := by
    match n with
    | 0=> 
      replace h:=Finset.card_eq_zero.mp h
      simp [h,h2]
    | .succ N' =>
      set L:=s'.toList with HH2
      match L with
      | [] =>
        replace HH2:=congrArg List.length HH2
        simp at HH2; rw [HH2.symm] at h; simp at h
      | a::L' =>
        have p1: {a} ∪ L'.toFinset = s' := by 
          refine' Finset.ext_iff.mpr _
          intro b 
          have mp : b∈ {a} ∪ L'.toFinset -> b∈ s' := by
            intro hb; simp at hb
            cases' hb with hb1 hb2
            · have p2: a ∈ Finset.toList s' := by 
                rw [HH2.symm]; simp
              simp at p2; rw [hb1]; exact p2
            · have p2: b ∈ Finset.toList s' := by
                rw [HH2.symm] ; simp
                exact Or.inr hb2
              simp at p2; exact p2
          have mpr: b∈ s' -> b∈ {a} ∪ L'.toFinset := by
            intro hb; replace hb:=Finset.mem_toList.mpr hb
            rw [HH2.symm] at hb; simp ; simp at hb
            exact hb
          exact ⟨mp,mpr⟩ 
        have p2: {a} ∩ L'.toFinset = ∅  := by 
          by_contra hc; 
-/
      

    
 


















