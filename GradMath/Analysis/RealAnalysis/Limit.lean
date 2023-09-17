import GradMath.Topology.PointSet.MetricSpace
import GradMath.Basic.SUP_INF
import GradMath.Basic.Sort
import Mathlib.Data.Real.Sqrt

noncomputable section

namespace LIMIT

open PointSetTopology SUP_INF Set SET METRIC FUNCTION REAL Classical LIST

def  topologicalSpaceERealAux.S :=
  let S1:={s:Set EReal | ∃x' y': ℝ,s={x:EReal | x'<x ∧ x<y'} }
  let S2:={s:Set EReal | ∃x':ℝ, s={x:EReal | x<x'} }
  let S3:={s:Set EReal | ∃x':ℝ, s={x:EReal | x'<x} }
  S1∪S2∪S3

lemma topologicalSpaceERealAux :∃! ts:TopologicalSpace EReal, ∃ B:topologicalBasis ts, 
topologicalSpaceERealAux.S= B.sets := by 
  let S1:={s:Set EReal | ∃x' y': ℝ,s={x:EReal| x'<x ∧ x<y'} }
  let S2:={s:Set EReal | ∃x':ℝ, s={x:EReal| x<x'} }
  let S3:={s:Set EReal | ∃x':ℝ, s={x:EReal| x'<x} }
  let S:=S1∪S2∪S3
  have p1:⋃₀ S = univ := by
    refine' setEqMpr (by simp) _
    intro x _
    match x with
    | +∞ =>
      have p1:+∞ ∈ {x:EReal | 0<x} := by simp
      have p2:{x:EReal | 0<x}∈ S3 := by 
        simp; refine' ⟨0,by simp ⟩ 
      simp only [mem_sUnion,mem_union]
      exact ⟨{x:EReal | 0<x},Or.inr p2,p1 ⟩ 
    | -∞ =>
      have p1:-∞ ∈ {x:EReal | x<0} := by simp
      have p2:{x:EReal | x<0}∈ S2 := by
        simp; refine' ⟨0,by simp ⟩
      simp only [mem_sUnion,mem_union]
      exact ⟨{x:EReal | x<0},Or.inl (Or.inr p2),p1 ⟩ 
    | (x:Real) =>
      have p1: (↑x:EReal)∈ {t:EReal | ↑(x-1)<t ∧ t<↑(x+1)} := by 
        have p2:(↑x:EReal) - 1 < ↑x := by
          have p3:x-1<x := by simp
          replace p3:=EReal.coe_lt_coe_iff.mpr p3
          exact p3
        have p3: ↑x <(↑x:EReal) + 1  := by
          have p4: x<x+ 1 := by simp
          replace p4:= EReal.coe_lt_coe_iff.mpr p4
          exact p4
        exact ⟨p2,p3 ⟩ 
      have p2:{t:EReal | ↑(x-1)<t ∧ t<↑(x+1)} ∈ S1 := by
        refine' ⟨x-1,x+1,_ ⟩ ; rfl
      simp only [mem_sUnion,mem_union]
      exact ⟨{t:EReal | ↑(x-1)<t ∧ t<↑(x+1)},Or.inl (Or.inl p2),p1 ⟩
  have p2:∀ {B1 B2 : Set EReal}, B1 ∈ S → B2 ∈ S → ∀ {x : EReal}, x ∈ B1 ∩ B2 → 
  ∃ B3, B3 ∈ S ∧ x ∈ B3 ∧ B3 ⊆ B1 ∩ B2 := by
    intro B1 B2 hB1 hB2 x hx
    simp only [mem_union] at hB1 hB2
    cases' hB1  with hB1 hB1_3
    · cases' hB1 with hB1_1 hB1_2
      · cases' hB2 with hB2 hB2_3
        · cases' hB2 with hB2_1 hB2_2
          · refine' Exists.elim hB1_1 _
            intro B1x hB1_1
            refine' Exists.elim hB1_1 _
            intro B1y hB1
            refine' Exists.elim hB2_1 _
            intro B2x hB2_1
            refine' Exists.elim hB2_1 _
            intro B2y hB2
            refine' ⟨_,_,hx,by simp ⟩ 
            simp only [mem_union]; refine' Or.inl (Or.inl _)
            rw [hB1,hB2]; 
            refine' ⟨ B1x ⊔ B2x,B1y ⊓ B2y, setEqIff.mpr _ ⟩ 
            intro r 
            have mp: r ∈ {x | ↑B1x < x ∧ x < ↑B1y} ∩ {x | ↑B2x < x ∧ x < ↑B2y} ->
            r ∈ {x | ↑(B1x ⊔ B2x) < x ∧ x < ↑(B1y ⊓ B2y)} := by
              intro h1; 
              match r with
              | +∞  =>
                simp at h1
              | -∞ =>
                simp at h1
              | (r':Real) =>
                simp; simp at h1; refine' ⟨⟨h1.left.left,h1.right.left ⟩ ,h1.left.right,h1.right.right ⟩ 
            have mpr:  r ∈ {x | ↑(B1x ⊔ B2x) < x ∧ x < ↑(B1y ⊓ B2y)} ->
            r ∈ {x | ↑B1x < x ∧ x < ↑B1y} ∩ {x | ↑B2x < x ∧ x < ↑B2y} := by
              intro h1
              match r with
              | +∞  =>
                simp at h1
              | -∞ =>
                simp at h1
              | (r':Real) =>
                simp; simp at h1; refine' ⟨⟨h1.left.left,h1.right.left ⟩ ,h1.left.right,h1.right.right ⟩
            exact ⟨mp,mpr⟩ 
          · refine' Exists.elim hB1_1 _
            intro B1x hB1_1
            refine' Exists.elim hB1_1 _
            intro B1y hB1
            refine' Exists.elim hB2_2 _
            intro B2y hB2
            refine' ⟨_,_,hx,by simp ⟩ 
            simp only [mem_union]; refine' Or.inl (Or.inl _)
            rw [hB1,hB2]; 
            refine' ⟨ B1x,B1y ⊓ B2y, setEqIff.mpr _ ⟩ 
            intro r              
            have mp: r ∈ {x | ↑B1x < x ∧ x < ↑B1y} ∩ {x | x < ↑B2y} -> 
            r ∈ {x | ↑B1x < x ∧ x < ↑(B1y ⊓ B2y)} := by
              intro h1
              match r with
              | +∞  =>
                simp at h1
              | -∞ =>
                simp at h1
              | (r':Real) =>
                simp; simp at h1; exact ⟨h1.left.left,h1.left.right,h1.right ⟩ 
            have mpr: r ∈ {x | ↑B1x < x ∧ x < ↑(B1y ⊓ B2y)} ->
            r ∈ {x | ↑B1x < x ∧ x < ↑B1y} ∩ {x | x < ↑B2y} := by
              intro h1
              match r with
              | +∞  =>
                simp at h1
              | -∞ =>
                simp at h1
              | (r':Real) =>
                simp; simp at h1; exact ⟨⟨h1.left,h1.right.left⟩ ,h1.right.right ⟩ 
            exact ⟨mp,mpr ⟩ 
        · refine' Exists.elim hB1_1 _
          intro B1x hB1_1
          refine' Exists.elim hB1_1 _
          intro B1y hB1
          refine' Exists.elim hB2_3 _
          intro B2x hB2
          refine' ⟨_,_,hx,by simp ⟩ 
          simp only [mem_union]; refine' Or.inl (Or.inl _)
          rw [hB1,hB2]; 
          refine' ⟨ B1x⊔ B2x,B1y, setEqIff.mpr _ ⟩ 
          intro r              
          have mp: r ∈ {x | ↑B1x < x ∧ x < ↑B1y} ∩ {x | ↑B2x < x} -> 
          r ∈ {x | ↑(B1x ⊔ B2x) < x ∧ x < ↑B1y} := by
            intro h1
            match r with
            | +∞  =>
              simp at h1
            | -∞ =>
              simp at h1
            | (r':Real) =>
              simp; simp at h1; exact ⟨⟨h1.left.left,h1.right⟩ ,h1.left.right ⟩ 
          have mpr: r ∈ {x | ↑(B1x ⊔ B2x) < x ∧ x < ↑B1y}->
          r ∈ {x | ↑B1x < x ∧ x < ↑B1y} ∩ {x | ↑B2x < x}  := by
            intro h1
            match r with
            | +∞  =>
              simp at h1
            | -∞ =>
              simp at h1
            | (r':Real) =>
              simp; simp at h1; exact ⟨⟨h1.left.left,h1.right⟩ ,h1.left.right ⟩ 
          exact ⟨mp,mpr⟩ 
      · cases' hB2 with hB2 hB2_3
        · cases' hB2 with hB2_1 hB2_2
          · refine' Exists.elim hB1_2 _
            intro B1y hB1
            refine' Exists.elim hB2_1 _
            intro B2x hB2_1
            refine' Exists.elim hB2_1 _
            intro B2y hB2
            refine' ⟨_,_,hx,by simp ⟩ 
            simp only [mem_union]; refine' Or.inl (Or.inl _)
            rw [hB1,hB2]; 
            refine' ⟨  B2x,B1y ⊓ B2y, setEqIff.mpr _ ⟩ 
            intro r 
            have mp: r ∈ {x | x < ↑B1y} ∩ {x | ↑B2x < x ∧ x < ↑B2y} -> 
            r ∈ {x | ↑B2x < x ∧ x < ↑(B1y ⊓ B2y)} := by
              intro h1; 
              match r with
              | +∞  =>
                simp at h1
              | -∞ =>
                simp at h1
              | (r':Real) =>
                simp; simp at h1; refine' ⟨h1.right.left,h1.left,h1.right.right ⟩ 
            have mpr:r ∈ {x | ↑B2x < x ∧ x < ↑(B1y ⊓ B2y)} ->
            r ∈ {x | x < ↑B1y} ∩ {x | ↑B2x < x ∧ x < ↑B2y} := by
              intro h1
              match r with
              | +∞  =>
                simp at h1
              | -∞ =>
                simp at h1
              | (r':Real) =>
                simp; simp at h1; refine' ⟨h1.right.left,h1.left,h1.right.right ⟩ 
            exact ⟨mp,mpr⟩ 
          · refine' Exists.elim hB1_2 _
            intro B1y hB1
            refine' Exists.elim hB2_2 _
            intro B2y hB2
            refine' ⟨_,_,hx,by simp ⟩ 
            simp only [mem_union]; refine' Or.inl (Or.inr _)
            rw [hB1,hB2]; simp
            refine' ⟨  B1y ⊓ B2y, setEqIff.mpr _ ⟩ 
            intro r ;simp
            have mp: r < ↑B1y ∧ r < ↑B2y -> r < ↑(B1y ⊓ B2y) := by
              intro h1
              match r with
              | +∞  =>
                simp at h1
              | -∞ => simp
              | (r':Real) =>
                simp;simp at h1; exact h1
            have mpr: r < ↑(B1y ⊓ B2y)->r < ↑B1y ∧ r < ↑B2y  := by
              intro h1
              match r with
              | +∞  =>
                simp at h1
              | -∞ => simp
              | (r':Real) =>
                simp;simp at h1; exact h1
            exact ⟨mp,mpr⟩ 
        · refine' Exists.elim hB1_2 _
          intro B1y hB1
          refine' Exists.elim hB2_3 _
          intro B2x hB2
          refine' ⟨_,_,hx,by simp ⟩ 
          simp only [mem_union]; refine' Or.inl (Or.inl _)
          rw [hB1,hB2]; simp
          refine' ⟨  B2x, B1y, setEqIff.mpr _ ⟩ 
          intro r ;simp
          have mp: r < ↑B1y ∧ ↑B2x < r -> ↑B2x < r ∧ r < ↑B1y:= by
            intro h1
            match r with
            | +∞  =>
              simp at h1
            | -∞ => 
              simp at h1
            | (r':Real) =>
              simp;simp at h1; exact ⟨h1.right,h1.left ⟩ 
          have mpr: ↑B2x < r ∧ r < ↑B1y-> r < ↑B1y ∧ ↑B2x < r   := by
            intro h1
            match r with
            | +∞  =>
              simp at h1
            | -∞ => 
              simp at h1
            | (r':Real) =>
              simp;simp at h1; exact ⟨h1.right,h1.left ⟩ 
          exact ⟨mp,mpr⟩ 
    · cases' hB2 with hB2 hB2_3
      · cases' hB2 with hB2_1 hB2_2
        · refine' Exists.elim hB1_3 _
          intro B1x hB1
          refine' Exists.elim hB2_1 _
          intro B2x hB2_1
          refine' Exists.elim hB2_1 _
          intro B2y hB2
          refine' ⟨_,_,hx,by simp ⟩ 
          simp only [mem_union]; refine' Or.inl (Or.inl _)
          rw [hB1,hB2]; simp
          refine' ⟨  B1x ⊔ B2x, B2y, setEqIff.mpr _ ⟩ 
          intro r ;simp
          have mp: ↑B1x < r ∧ ↑B2x < r ∧ r < ↑B2y -> ↑(B1x ⊔ B2x) < r ∧ r < ↑B2y:= by
            intro h1
            match r with
            | +∞  =>
              simp at h1
            | -∞ => 
              simp at h1
            | (r':Real) =>
              simp;simp at h1; exact ⟨⟨h1.left,h1.right.left ⟩,h1.right.right ⟩ 
          have mpr:↑(B1x ⊔ B2x) < r ∧ r < ↑B2y->↑B1x < r ∧ ↑B2x < r ∧ r < ↑B2y   := by
            intro h1
            match r with
            | +∞  =>
              simp at h1
            | -∞ => 
              simp at h1
            | (r':Real) =>
              simp;simp at h1;  exact ⟨h1.left.left,h1.left.right ,h1.right ⟩ 
          exact ⟨mp,mpr⟩ 
        · refine' Exists.elim hB1_3 _
          intro B1x hB1
          refine' Exists.elim hB2_2 _
          intro B2y hB2
          refine' ⟨_,_,hx,by simp ⟩ 
          simp only [mem_union]; refine' Or.inl (Or.inl _)
          rw [hB1,hB2]; simp
          refine' ⟨  B1x, B2y, setEqIff.mpr _ ⟩ 
          intro r ;simp
      · refine' Exists.elim hB1_3 _
        intro B1x hB1
        refine' Exists.elim hB2_3 _
        intro B2x hB2
        refine' ⟨_,_,hx,by simp ⟩ 
        simp only [mem_union]; refine' Or.inr _
        rw [hB1,hB2]; simp
        refine' ⟨  B1x ⊔ B2x, setEqIff.mpr _ ⟩ 
        intro r ;simp
        have mp: ↑B1x < r ∧ ↑B2x < r -> ↑(B1x ⊔ B2x) < r := by
          intro h1         
          match r with
          | +∞ =>  simp
          | -∞ => simp at h1
          | (r':Real) =>
            simp; simp at h1; exact h1
        have mpr:  ↑(B1x ⊔ B2x) < r ->↑B1x < r ∧ ↑B2x < r := by
          intro h1
          match r with
          | +∞ => simp
          | -∞ => simp at h1
          | (r':Real) =>
            simp; simp at h1; exact h1
        exact ⟨mp,mpr⟩ 
  exact ((basisForSomeSpaceIff S).mp ⟨p1, p2⟩ )
          
instance : TopologicalSpace EReal :=choose topologicalSpaceERealAux

lemma erealTopologicalBasis: ∃ B:topologicalBasis instTopologicalSpaceEReal, 
topologicalSpaceERealAux.S= B.sets := 
(choose_spec  topologicalSpaceERealAux).left 

@[simp]
lemma erealOpenIntervalOfRight { b:EReal}:IsOpen {x:EReal | x<b} := by
  set bb:= b with HH
  refine' Exists.elim erealTopologicalBasis _
  intro tB htB
  match bb with
  | -∞ =>
    simp
  | +∞ =>
    have p1:{x:EReal | x<bb} = ⋃₀ {s:Set EReal | ∃x':ℝ, s={x:EReal | x<↑x'} }  := by
      refine' setEqIff.mpr _
      intro x
      have mp: x ∈ {x:EReal | x<bb} -> x ∈⋃₀ {s:Set EReal | ∃x':ℝ, s={x:EReal | x<↑x'}}  := by
        intro h;simp
        match x with
        | +∞ =>
          simp at h
        | -∞ =>
          refine' ⟨{x | x < 0},⟨0,rfl ⟩,by simp  ⟩ 
        | (x':Real) =>
          refine' ⟨{x | x < x'+1},⟨x'+1,rfl ⟩,_  ⟩
          have p1: x'<x'+1 := by simp
          exact EReal.coe_lt_coe_iff.mpr p1
      have mpr:x ∈⋃₀ {s:Set EReal | ∃x':ℝ, s={x:EReal | x<↑x'}}->x ∈ {x:EReal | x<bb} := by
        intro h; 
        refine' Exists.elim h _
        intro t ht; simp at ht
        refine' Exists.elim ht.left _
        intro z hz; replace hz:=hz ▸ ht.right
        match x with
        | +∞ =>
          simp at hz
        | -∞ =>
          simp ; rw [HH.symm]; simp
        | (x':Real) =>
          simp at hz; simp; rw [HH.symm]
          calc 
            _ < _ :=EReal.coe_lt_coe_iff.mpr  hz
            _ ≤ _ := by simp
      exact ⟨mp,mpr⟩ 
    have p2:∀{t:Set EReal},t ∈  {s:Set EReal | ∃x':ℝ, s={x:EReal | x<↑x'} } -> IsOpen t := by
      intro t ht
      have p3: t∈ tB.sets := by
        rw [htB.symm]; exact Or.inl (Or.inr ht)
      exact tB.sets_forall_open p3
    have p3:{x | x < ⊤} = {x | x<bb} := by 
      rw [HH]
    rw [p3,p1]; exact openSUnion p2
  | (r:ℝ) =>
    have p1:{x | x < ↑r}∈ tB.sets := by
      rw [htB.symm]; exact Or.inl (Or.inr ⟨r,rfl ⟩ )
    exact tB.sets_forall_open p1
          
@[simp]
lemma erealOpenIntervalOfLeft { a:EReal}:IsOpen {x:EReal | a<x} := by
  set bb:= a with HH
  refine' Exists.elim erealTopologicalBasis _
  intro tB htB
  match bb with
  | +∞ =>
    simp
  | -∞ =>
    have p1:{x:EReal | bb<x} = ⋃₀ {s:Set EReal | ∃x':ℝ, s={x:EReal | ↑x'<x} }  := by
      refine' setEqIff.mpr _
      intro x
      have mp:x∈ {x:EReal | bb<x} ->x∈⋃₀ {s:Set EReal | ∃x':ℝ, s={x:EReal | ↑x'<x} } := by
        intro h;simp
        match x with
        | -∞ =>
          simp at h
        | +∞ =>
          refine' ⟨{x | 0<x},⟨0,rfl ⟩,by simp  ⟩ 
        | (x':Real) =>
          refine' ⟨{x | x'-1<x},⟨x'-1,rfl ⟩,_  ⟩
          have p1: x'-1<x' := by simp
          exact EReal.coe_lt_coe_iff.mpr p1
      have mpr:x∈⋃₀ {s:Set EReal| ∃x':ℝ, s={x:EReal| ↑x'<x} } ->x∈ {x:EReal| bb<x}  := by
        intro h; 
        refine' Exists.elim h _
        intro t ht; simp at ht
        refine' Exists.elim ht.left _
        intro z hz; replace hz:=hz ▸ ht.right
        match x with
        | -∞ =>
          simp at hz
        | +∞ =>
          simp ; rw [HH.symm]; simp
        | (x':Real) =>
          simp at hz; simp; rw [HH.symm]
          calc 
            _ ≤ _ := by simp
            _ < _ :=EReal.coe_lt_coe_iff.mpr  hz
      exact ⟨mp,mpr⟩ 
    have p2:∀{t:Set EReal},t ∈{s:Set EReal| ∃x':ℝ, s={x:EReal| ↑x'<x} }-> IsOpen t := by
      intro t ht
      have p3: t∈ tB.sets := by
        rw [htB.symm]; exact  (Or.inr ht)
      exact tB.sets_forall_open p3
    have p3:{x | ⊥ < x}= {x| bb<x} := by 
      rw [HH]
    rw [p3,p1]; exact openSUnion p2
  | (r:ℝ) =>
    have p1:{x | ↑r< x}∈ tB.sets := by
      rw [htB.symm]; exact  (Or.inr ⟨r,rfl ⟩ )
    exact tB.sets_forall_open p1
 
@[simp]
lemma erealOpenIntervalOfLeftRight  {a b:EReal}:IsOpen {x:EReal| a<x∧x<b} := by
  have p1: {x:EReal| a<x∧x<b} = {x:EReal| a<x} ∩ {x:EReal| x<b} := by 
    refine' setEqIff.mpr _
    intro z 
    have mp:z ∈ {x |  a < x ∧ x < b} -> z ∈ {x | a < x} ∩ {x | x < b} := by
      intro h1; simp ; simp at h1; exact h1
    have mpr:  z ∈ {x | a < x} ∩ {x | x < b}-> z ∈ {x | a < x ∧ x < b} := by
      intro h1; simp; simp at h1; exact h1
    exact ⟨mp,mpr⟩ 
  rw [p1]; exact openInter (by simp) (by simp)

lemma convergesInRealIff {x:sequenceN ℝ } {x0:ℝ}:
x.convergesTo x0 ↔ ∀{ε:ℝ}, ε>0 -> ∃N,∀{n:ℕ}, N≤n->|x n - x0| < ε := by
  have mp: x.convergesTo x0 -> ∀{ε:ℝ}, ε>0 -> ∃N, ∀{n:ℕ},N≤n->|x n - x0| < ε := by
    intro h1 ε hε ; simp at h1
    let nb:neighb x0 := {
      set:= Metric.ball x0 ε 
      property:= by 
        refine' ⟨by simp [hε],metricBallIsOpen ⟩ }
    refine' Exists.elim ( h1 nb) _
    intro N hN
    refine' ⟨N,_ ⟩ 
    intro n hn; replace hN:= hN hn; simp [dist] at hN
    exact hN
  have mpr: (∀{ε:ℝ}, ε>0 -> ∃N, ∀{n:ℕ},N≤n->|x n - x0| < ε)-> x.convergesTo x0 := by
    intro h1; simp 
    intro u 
    refine' Exists.elim (openIff.mp u.property.right u.property.left) _
    intro ε hε 
    refine' Exists.elim hε _
    intro hε p1
    refine' Exists.elim (h1 hε ) _
    intro N hN; refine' ⟨N,_ ⟩ 
    intro n hn; refine' setSubsetIff.mp p1 _ _
    simp; exact hN hn
  exact ⟨mp,mpr⟩ 

lemma coeConvergesToRealInEReal {x:sequenceN ℝ } {x0:Real} 
(h:sequenceN.convergesTo (fun n=> (x n:EReal)) (x0:EReal)):x.convergesTo x0 := by
  rw [convergesInRealIff]
  intro ε hε 
  let nb:neighb (x0:EReal) := {
    set:= {r:EReal| x0-ε<r∧r<x0+ε}
    property:= by 
      refine' ⟨_,by simp ⟩ 
      have p1:x0< x0 + ε := by simp [hε]
      have p2:x0-ε<x0 := by simp [hε]
      exact ⟨EReal.coe_lt_coe_iff.mpr p2,EReal.coe_lt_coe_iff.mpr p1 ⟩  }
  refine' Exists.elim (h nb) _
  intro N hN; refine' ⟨N,_ ⟩ 
  intro n hn; replace hN:=hN hn; simp at hN
  by_cases c: 0≤ x n - x0
  · rw [abs_of_nonneg c]
    have p1:x n  < ε + x0 := by
      refine' EReal.coe_lt_coe_iff.mp _
      rw [add_comm]; simp; exact hN.right
    replace p1:=addLtAddMpr p1 (-x0); 
    rw [add_assoc,← sub_eq_add_neg] at p1; 
    simp at p1; exact p1
  · push_neg at c
    rw [abs_of_neg c]
    have p1:x0 - ε < (x n)  := by
      refine' EReal.coe_lt_coe_iff.mp _
      rw [EReal.coe_sub]; exact hN.left
    replace p1:=addLtAddMpr p1 (ε -x n)
    simp at p1; simp; exact p1

lemma convergesToRealInERealIff {x:sequenceN EReal } {x0:Real} :
x.convergesTo ↑x0 ↔ ∀{ε:ℝ}, ε>0 -> ∃N:ℕ, ∀{n:ℕ}, N≤n -> ↑(x0-ε)< x n ∧ x n < ↑(x0+ε) := by
  have mp:x.convergesTo ↑x0 -> (∀{ε:ℝ}, ε>0 -> ∃N:ℕ, ∀{n:ℕ}, N≤n -> ↑(x0-ε)< x n ∧ x n < ↑(x0+ε)) := by
    intro h1 ε hε 
    let nb:neighb (↑x0) := {
      set:={r:EReal| ↑(x0-ε)< r ∧ r < ↑(x0+ε)}
      property := by
        refine' ⟨_ ,by simp⟩ 
        have p1:(x0-ε)< x0 := by simp [hε ]
        have p2: x0< (x0+ε) := by simp [hε]
        exact ⟨EReal.coe_lt_coe_iff.mpr p1,EReal.coe_lt_coe_iff.mpr p2 ⟩ }
    refine' Exists.elim (h1 nb) _
    intro N hN
    refine' ⟨N,_ ⟩ 
    intro n hn; exact hN hn
  have mpr: (∀{ε:ℝ}, ε>0 -> ∃N:ℕ, ∀{n:ℕ}, N≤n -> ↑(x0-ε)< x n ∧ x n < ↑(x0+ε))->x.convergesTo ↑x0 := by
    intro h1 nb
    refine' Exists.elim  erealTopologicalBasis _
    intro tB htB
    refine' Exists.elim (tB.any_open_is_sunion nb.property.right) _
    intro B hB
    refine' Exists.elim (hB.right ▸ nb.property.left ) _
    intro t ht; let p1:= htB.symm ▸ setSubsetIff.mp hB.left _ ht.left
    cases' p1 with c1' c3
    · cases' c1' with c1 c2
      · refine' Exists.elim c1 _
        intro a c1; refine' Exists.elim  c1 _ ;intro b c1
        have p2:0<(x0-a)⊓(b-x0) := by 
          let p3:=c1 ▸ ht.right; simp at p3; simp; exact p3
        refine' Exists.elim (h1 p2) _
        intro N hN; refine' ⟨N,_ ⟩ ;intro n hn
        replace hN:=hN hn; rw [hB.right]
        have p3:t⊆ ⋃₀ B := by
          intro z hz; simp; exact ⟨_,ht.left,hz ⟩ 
        refine' setSubsetIff.mp p3 _ _
        rw [c1];simp; simp at hN
        have p4:(↑a:EReal ) ≤ ↑x0 - ↑((x0 - a) ⊓ (b - x0)) := by
          have p5: (x0 - a) ⊓ (b - x0) ≤ x0 -a := by simp
          replace p5:=addLeAddMpr p5 (-((x0 - a) ⊓ (b - x0))+a)
          rw [← add_assoc,add_neg_self] at p5; 
          have p6:x0 - a + (-((x0 - a) ⊓ (b - x0)) + a) = x0 - (x0 - a) ⊓ (b - x0) := by ring
          rw [p6] at p5;simp at p5; exact EReal.coe_le_coe_iff.mpr p5
        have p5: ↑x0 + ↑((x0 - a) ⊓ (b - x0)) ≤ (↑b:EReal) := by
          have p6:(x0 - a) ⊓ (b - x0) ≤ (b - x0) := by simp
          replace p6:=addLeAddMpr p6 x0; rw [sub_eq_add_neg b x0,add_assoc] at p6
          simp at p6; rw [add_comm] at p6; exact EReal.coe_le_coe_iff.mpr p6
        replace p4:=calc
          _ ≤ _ :=p4
          _ < _ :=hN.left
        replace p5:=calc
          _ < _ := hN.right
          _ ≤ _ := p5
        exact ⟨p4,p5 ⟩ 
      · refine' Exists.elim c2 _
        intro b c2;let c2':=c2 ▸ ht.right ; simp at c2'
        have p2:0< b-x0 := by simp [c2']
        refine' Exists.elim (h1 p2) _
        intro N hN; refine' ⟨N,_ ⟩ 
        intro n hn;replace hN:=hN hn; rw [hB.right]
        have p3:t⊆ ⋃₀ B := by
          intro z hz; simp; exact ⟨_,ht.left,hz ⟩ 
        refine' setSubsetIff.mp p3 _ _
        rw [c2];simp; simp at hN; exact hN.right
    · refine' Exists.elim c3 _
      intro a c3;let c3':=c3 ▸ ht.right ; simp at c3'
      have p2:0< x0-a := by simp [c3']
      refine' Exists.elim (h1 p2) _
      intro N hN; refine' ⟨N,_ ⟩ 
      intro n hn;replace hN:=hN hn;rw [hB.right]
      have p3:t⊆ ⋃₀ B := by
        intro z hz; simp; exact ⟨_,ht.left,hz ⟩ 
      refine' setSubsetIff.mp p3 _ _
      rw [c3];simp; simp at hN; exact hN.left
  exact ⟨mp,mpr⟩ 

lemma convergesToPosInftyIff {x:sequenceN EReal }:
x.convergesTo (+∞) ↔ ∀(r:ℝ), ∃N:ℕ, ∀{n:ℕ}, N≤n -> r<x n := by
  have mp:x.convergesTo (+∞) -> (∀(r:ℝ), ∃N:ℕ, ∀{n:ℕ}, N≤n -> r<x n) := by
    intro h1 r ; simp at h1
    let nb:neighb (+∞):= {
      set := {t:EReal| r<t}
      property:= by simp}
    refine' Exists.elim (h1 nb) _
    intro N hN; refine' ⟨N,_ ⟩ 
    intro n hn; exact hN hn
  have mpr: (∀(r:ℝ), ∃N:ℕ, ∀{n:ℕ}, N≤n -> r<x n) ->x.convergesTo (+∞) := by
    intro h1; simp
    intro nb 
    refine' Exists.elim erealTopologicalBasis _
    intro tB htB; 
    refine' Exists.elim (tB.any_open_is_sunion nb.property.right) _
    intro b hb
    have p1: ∃a:ℝ ,{t:EReal|a<t} ∈ b := by
      refine' Exists.elim (mem_sUnion.mp (hb.right ▸ nb.property.left)) _
      intro u hu
      let p2:=htB.symm ▸ (setSubsetIff.mp hb.left _ hu.left)
      cases' p2 with p2 c3
      · cases' p2 with c1 c2
        · refine' Exists.elim c1 _
          intro A c1
          refine' Exists.elim c1 _
          intro B c1
          replace hu:= c1 ▸ hu.right
          simp at hu
        · refine' Exists.elim c2 _
          intro B c2
          replace hu:= c2 ▸ hu.right
          simp at hu
      · refine' Exists.elim c3 _
        intro A hA
        exact ⟨_,hA ▸ hu.left ⟩ 
    refine' Exists.elim p1 _
    intro a ha
    have p2:{t | ↑a < t} ⊆  nb.set := by
      rw [hb.right]
      intro z hz; simp 
      exact ⟨_,ha,hz ⟩ 
    refine' Exists.elim (@h1 a) _
    intro N hN; refine' ⟨N,_ ⟩ 
    intro n hn; refine' setSubsetIff.mp p2 _ _
    exact hN hn
  exact ⟨mp,mpr⟩ 

lemma convergesToNegInftyIff {x:sequenceN EReal }:
x.convergesTo (-∞) ↔ ∀(r:ℝ), ∃N:ℕ, ∀{n:ℕ}, N≤n -> x n<r := by
  have mp:x.convergesTo (-∞) -> (∀(r:ℝ), ∃N:ℕ, ∀{n:ℕ}, N≤n -> x n<r) := by
    intro h1 r ; simp at h1
    let nb:neighb (-∞):= {
      set := {t:EReal|t<r}
      property:= by simp}
    refine' Exists.elim (h1 nb) _
    intro N hN; refine' ⟨N,_ ⟩ 
    intro n hn; exact hN hn
  have mpr: (∀(r:ℝ), ∃N:ℕ, ∀{n:ℕ}, N≤n -> x n<r) ->x.convergesTo (-∞) := by
    intro h1; simp
    intro nb 
    refine' Exists.elim erealTopologicalBasis _
    intro tB htB; 
    refine' Exists.elim (tB.any_open_is_sunion nb.property.right) _
    intro b hb
    have p1: ∃a:ℝ ,{t:EReal|t<a} ∈ b := by
      refine' Exists.elim (mem_sUnion.mp (hb.right ▸ nb.property.left)) _
      intro u hu
      let p2:=htB.symm ▸ (setSubsetIff.mp hb.left _ hu.left)
      cases' p2 with p2 c3
      · cases' p2 with c1 c2
        · refine' Exists.elim c1 _
          intro A c1
          refine' Exists.elim c1 _
          intro B c1
          replace hu:= c1 ▸ hu.right
          simp at hu
        · refine' Exists.elim c2 _
          intro B hB
          exact ⟨_,hB ▸ hu.left ⟩ 
      · refine' Exists.elim c3 _
        intro A c3
        replace hu:= c3 ▸ hu.right
        simp at hu
    refine' Exists.elim p1 _
    intro a ha
    have p2:{t |t< ↑a } ⊆  nb.set := by
      rw [hb.right]
      intro z hz; simp 
      exact ⟨_,ha,hz ⟩ 
    refine' Exists.elim (@h1 a) _
    intro N hN; refine' ⟨N,_ ⟩ 
    intro n hn; refine' setSubsetIff.mp p2 _ _
    exact hN hn
  exact ⟨mp,mpr⟩ 

def limsup (x:sequenceN EReal) :EReal :=
INF (Im(fun n:Nat => SUP (Im(x,{l|n≤ l})) ,univ))

def liminf (x:sequenceN EReal) :EReal :=
SUP (Im(fun n:Nat => INF (Im(x,{l|n≤ l})) ,univ))

structure LIM (x:sequenceN EReal) where
val:EReal
limsup_eq_val : limsup x = val
liminf_eq_val : liminf x = val

structure LIM' (x:sequenceN EReal) where
val:Real
limsup_eq_val : limsup x = ↑val
liminf_eq_val : liminf x = ↑val

variable {X:sequenceN EReal}
instance: CoeDep (LIM X) X0 EReal where
  coe :=X0.val
instance: CoeDep (LIM' X) X0 Real where
  coe :=X0.val

lemma limsupNegEqNegLiminf {x:sequenceN EReal}:
limsup (fun n => -(x n)) = -(liminf x) := by
  simp only [liminf,limsup]
  have p1:Im(fun n => SUP (Im(fun n => -(x n),{l | n ≤ l})),univ)
  = setERealFlip (Im(fun n => INF (Im(x,{l | n ≤ l})),univ)) := by
    refine' setEqIff.mpr _
    intro z
    have mp: z∈Im(fun n => SUP (Im(fun n => -(x n),{l | n ≤ l})),univ)
    -> z∈  setERealFlip (Im(fun n => INF (Im(x,{l | n ≤ l})),univ)) := by 
      intro h1; simp only [setERealFlip,mem_def]; 
      refine' mem_def.mp _ ;rw [mem_image]
      simp only [mem_image] at h1
      refine' Exists.elim h1 _
      intro n hn; refine' ⟨n,by simp,_ ⟩ 
      have p2:Im(fun n => -x n,{l | n ≤ l}) = setERealFlip (Im(x,{l | n ≤ l})) := by 
        refine' setEqIff.mpr _
        intro y
        have mp:y ∈ Im(fun n => -x n,{l | n ≤ l}) -> y ∈ setERealFlip (Im(x,{l | n ≤ l})) := by
          intro h1; refine' memFlipIff.mpr _
          simp at h1; simp
          refine' Exists.elim h1 _
          intro m hm
          refine' ⟨_,hm.left,by rw [hm.right.symm];simp ⟩ 
        have mpr: y ∈ setERealFlip (Im(x,{l | n ≤ l})) -> y ∈ Im(fun n => -x n,{l | n ≤ l}) := by
          intro h1; replace h1:=memFlipIff.mp h1; simp at h1
          simp; refine' Exists.elim h1 _
          intro m hm; exact ⟨_,hm.left,by rw [hm.right];simp ⟩ 
        exact ⟨mp,mpr⟩ 
      rw [hn.right.symm,p2]; exact infIsNegSupFlip
    have mpr:  z∈  setERealFlip (Im(fun n => INF (Im(x,{l | n ≤ l})),univ)) 
    -> z∈Im(fun n => SUP (Im(fun n => -(x n),{l | n ≤ l})),univ) := by
      intro h1; simp only [setERealFlip,mem_def] at h1
      replace h1:=mem_def.mpr h1; rw [mem_image] at h1
      simp only [mem_image] 
      refine' Exists.elim h1 _
      intro n hn; refine' ⟨n,by simp,_ ⟩ 
      have p2:Im(fun n => -x n,{l | n ≤ l}) = setERealFlip (Im(x,{l | n ≤ l})) := by 
        refine' setEqIff.mpr _
        intro y
        have mp:y ∈ Im(fun n => -x n,{l | n ≤ l}) -> y ∈ setERealFlip (Im(x,{l | n ≤ l})) := by
          intro h1; refine' memFlipIff.mpr _
          simp at h1; simp
          refine' Exists.elim h1 _
          intro m hm
          refine' ⟨_,hm.left,by rw [hm.right.symm];simp ⟩ 
        have mpr: y ∈ setERealFlip (Im(x,{l | n ≤ l})) -> y ∈ Im(fun n => -x n,{l | n ≤ l}) := by
          intro h1; replace h1:=memFlipIff.mp h1; simp at h1
          simp; refine' Exists.elim h1 _
          intro m hm; exact ⟨_,hm.left,by rw [hm.right];simp ⟩ 
        exact ⟨mp,mpr⟩ 
      let p3:=congrArg (-.) hn.right; simp only at p3
      have p4: - -z = z := by simp
      rw [p4] at p3; rw [p3.symm,p2]; 
      replace p4:=@infIsNegSupFlip (Im(x,{l | n ≤ l}))
      rw [p4]; simp
    exact ⟨mp,mpr⟩ 
  rw [p1,(@supIsNegInfFlip (Im(fun n => INF (Im(x,{l | n ≤ l})),univ)))]
  simp
 
lemma liminfNegEqNegLimsup {x:sequenceN EReal}:
liminf (fun n => -(x n)) = -(limsup x) := by
  simp only [liminf,limsup]
  have p1:Im(fun n => INF (Im(fun n => -(x n),{l | n ≤ l})),univ)
  = setERealFlip (Im(fun n => SUP (Im(x,{l | n ≤ l})),univ)) := by
    refine' setEqIff.mpr _
    intro z
    have mp: z∈Im(fun n => INF (Im(fun n => -(x n),{l | n ≤ l})),univ)
    -> z∈  setERealFlip (Im(fun n => SUP (Im(x,{l | n ≤ l})),univ)) := by 
      intro h1; simp only [setERealFlip,mem_def]; 
      refine' mem_def.mp _ ;rw [mem_image]
      simp only [mem_image] at h1
      refine' Exists.elim h1 _
      intro n hn; refine' ⟨n,by simp,_ ⟩ 
      have p2:Im(fun n => -x n,{l | n ≤ l}) = setERealFlip (Im(x,{l | n ≤ l})) := by 
        refine' setEqIff.mpr _
        intro y
        have mp:y ∈ Im(fun n => -x n,{l | n ≤ l}) -> y ∈ setERealFlip (Im(x,{l | n ≤ l})) := by
          intro h1; refine' memFlipIff.mpr _
          simp at h1; simp
          refine' Exists.elim h1 _
          intro m hm
          refine' ⟨_,hm.left,by rw [hm.right.symm];simp ⟩ 
        have mpr: y ∈ setERealFlip (Im(x,{l | n ≤ l})) -> y ∈ Im(fun n => -x n,{l | n ≤ l}) := by
          intro h1; replace h1:=memFlipIff.mp h1; simp at h1
          simp; refine' Exists.elim h1 _
          intro m hm; exact ⟨_,hm.left,by rw [hm.right];simp ⟩ 
        exact ⟨mp,mpr⟩ 
      rw [hn.right.symm,p2]; exact supIsNegInfFlip
    have mpr:  z∈  setERealFlip (Im(fun n => SUP (Im(x,{l | n ≤ l})),univ)) 
    -> z∈Im(fun n => INF (Im(fun n => -(x n),{l | n ≤ l})),univ) := by
      intro h1; simp only [setERealFlip,mem_def] at h1
      replace h1:=mem_def.mpr h1; rw [mem_image] at h1
      simp only [mem_image] 
      refine' Exists.elim h1 _
      intro n hn; refine' ⟨n,by simp,_ ⟩ 
      have p2:Im(fun n => -x n,{l | n ≤ l}) = setERealFlip (Im(x,{l | n ≤ l})) := by 
        refine' setEqIff.mpr _
        intro y
        have mp:y ∈ Im(fun n => -x n,{l | n ≤ l}) -> y ∈ setERealFlip (Im(x,{l | n ≤ l})) := by
          intro h1; refine' memFlipIff.mpr _
          simp at h1; simp
          refine' Exists.elim h1 _
          intro m hm
          refine' ⟨_,hm.left,by rw [hm.right.symm];simp ⟩ 
        have mpr: y ∈ setERealFlip (Im(x,{l | n ≤ l})) -> y ∈ Im(fun n => -x n,{l | n ≤ l}) := by
          intro h1; replace h1:=memFlipIff.mp h1; simp at h1
          simp; refine' Exists.elim h1 _
          intro m hm; exact ⟨_,hm.left,by rw [hm.right];simp ⟩ 
        exact ⟨mp,mpr⟩ 
      let p3:=congrArg (-.) hn.right; simp only at p3
      have p4: - -z = z := by simp
      rw [p4] at p3; rw [p3.symm,p2]; 
      replace p4:=@supIsNegInfFlip (Im(x,{l | n ≤ l}))
      rw [p4]; simp
    exact ⟨mp,mpr⟩ 
  rw [p1,(@infIsNegSupFlip (Im(fun n => SUP (Im(x,{l | n ≤ l})),univ)))]
  simp

lemma subSequenceIndexGeOrig {φ :ℕ ->ℕ} (h:StrictMono φ):∀(n:ℕ),n ≤ φ n := by
  intro n
  match n with
  | 0 => simp
  |.succ n' =>
    calc
      n'.succ ≤ (φ n').succ := Nat.succ_le_succ (subSequenceIndexGeOrig h n')
      _ ≤  (φ n'.succ) :=Nat.le_of_lt_succ (Nat.succ_le_succ (h (by simp:n'<n'.succ)))

lemma liminfLeLimSubSequence {x:sequenceN EReal} {φ :ℕ ->ℕ} {x0:EReal} (h1:StrictMono φ)
(h2:sequenceN.convergesTo (x∘φ) x0):liminf x ≤ x0:= by
  match x0 with
  | +∞ => simp
  | -∞ =>
    rw [convergesToNegInftyIff] at h2
    have p1:∀(r:Real),liminf x≤r := by
      intro r
      refine' Exists.elim (@h2 r) _
      intro N hN; rw [liminf]
      have p2:∀{t}, t∈ Im(fun n => INF (Im(x,{l | n ≤ l})),univ) -> t ≤r := by
        intro t ht; simp at ht
        refine' Exists.elim ht _
        intro M hM;rw [hM.symm]
        have p3:x (φ (N⊔M)) ∈ Im(x,{l | M ≤ l}) := by 
          simp; refine' ⟨φ (N⊔M),_,rfl ⟩ 
          calc 
            M ≤ N ⊔ M := by simp
            _ ≤ φ (N ⊔ M) :=subSequenceIndexGeOrig h1 _
        replace p3:=infIsLowerBound p3
        calc 
          INF (Im(x,{l | M ≤ l})) ≤ _ := p3
          _ ≤ ↑r := (hN (by simp:N≤ (N ⊔ M))).le
      exact supIsLeastUpperBound p2
    set li:=liminf x  
    match li with
    | -∞ => simp
    | +∞ => simp at p1
    | (r:Real) =>
      replace p1:= EReal.coe_le_coe_iff.mp (p1 (r-1))
      simp at p1
      replace p1:=calc
        0 < 1 := by simp
        _ ≤ _ := p1
      simp at p1
  | (r:Real) =>
    by_contra hc; push_neg at hc
    set li:=liminf x with HH
    match li with
    | -∞ => simp at hc
    | +∞ =>
      simp only [sequenceN.convergesTo] at h2
      let nb:neighb (↑r:EReal) :={
        set:={e:EReal|r-1<e ∧ e<r+1}
        property:= by
          refine' ⟨_,by simp ⟩ 
          have p1:r - 1 < r := by simp
          have p2:r<r+1 := by simp
          exact ⟨EReal.coe_lt_coe_iff.mpr p1,EReal.coe_lt_coe_iff.mpr p2 ⟩ }
      refine' Exists.elim (h2 nb) _
      intro N hN; rw [liminf] at HH
      let p1:=notBoundedAboveIff.mpr HH.symm; simp [boundedAbove] at p1
      refine' Exists.elim (p1 (r+1))  _
      intro N2 hN2
      have p2:(x (φ (N2 ⊔ N))) ∈ Im(x,{l | N2 ≤ l}) := by 
        rw [mem_image]; refine' ⟨(φ (N2 ⊔ N)),_ ⟩ 
        simp; calc
          N2 ≤ N2 ⊔ N := by simp
          _ ≤ φ (N2 ⊔ N) := subSequenceIndexGeOrig h1 _
      replace p2:=infIsLowerBound p2
      replace hN:=hN (by simp :N≤ (N2 ⊔  N))
      simp at hN
      let p3:= calc
        x (φ (N2 ⊔ N)) < ↑r + 1 := hN.right
        _ = ↑(r + 1) := by simp
        _ < _ :=hN2
        _ ≤ _ := p2
      simp at p3
    | (r':Real) =>
      simp at hc
      have p1:0<(r' - r) / 2:= by
        exact div_pos (by simp [hc]) (by simp)
      simp only [sequenceN.convergesTo] at h2
      let nb:neighb (↑r:EReal) :={
        set:={e:EReal|↑(r - (r'-r)/2)<e ∧e< ↑(r+ (r'-r)/2)}
        property:= by
          refine' ⟨_,by simp ⟩ 
          simp only [mem_def,setOf]
          have p2:(r - (r' - r) / 2) < r := by 
            simp [p1]; 
          have p3: r< (r+ (r'-r)/2) := by
            simp [p1]; 
          exact ⟨EReal.coe_lt_coe_iff.mpr p2,EReal.coe_lt_coe_iff.mpr p3 ⟩ } 
      refine' Exists.elim (h2 nb) _
      intro N1 hN1; rw [liminf] at HH
      have p2: ∀ {y : EReal}, y ∈ Im(fun n => INF (Im(x,{l | n ≤ l})),univ) → y ≤ ↑(r+ (r'-r)/2):= by
        intro y hy
        refine' Exists.elim hy _
        intro N2 hN2; simp at hN2
        replace hN1:=hN1 (by simp:N1 ≤ N1⊔N2 ); simp only [mem_def,setOf] at hN1
        have p3:(x ∘ φ) (N1 ⊔ N2) ∈  Im(x,{l | N2 ≤ l}) := by
          simp; refine' ⟨φ (N1 ⊔ N2),_,rfl ⟩ 
          calc
            N2 ≤ N1 ⊔ N2 := by simp
            N1 ⊔ N2 ≤ φ (N1 ⊔ N2) :=subSequenceIndexGeOrig h1 _
        replace p3:=infIsLowerBound p3
        calc
          _ = _ :=hN2.symm
          _ ≤ _ := p3
          _ ≤ _ := hN1.right.le
      replace p2:=supIsLeastUpperBound p2; rw [HH.symm] at p2
      replace p2:=addLeAddMpr (EReal.coe_le_coe_iff.mp p2) (-r'); 
      rw [← sub_eq_add_neg,sub_self] at p2;
      have p3:=calc
        0 ≤ _ :=p2
        _ = -((r' - r) / 2) := by ring
        _ < _ :=ltFlip p1
        _ = 0 := by simp
      simp at p3

lemma limsupGeLimSubSequence {x:sequenceN EReal} {φ :ℕ ->ℕ} {x0:EReal} (h1:StrictMono φ)
(h2:sequenceN.convergesTo (x∘φ) x0):x0 ≤ limsup x := by
  match x0 with
  | -∞ => simp
  | +∞ =>
    rw [convergesToPosInftyIff] at h2
    have p1:∀(r:Real),r ≤ limsup x := by
      intro r
      refine' Exists.elim (@h2 r) _
      intro N hN; rw [limsup]
      have p2:∀{t}, t∈ Im(fun n => SUP (Im(x,{l | n ≤ l})),univ) -> r ≤ t := by
        intro t ht; simp at ht
        refine' Exists.elim ht _
        intro M hM;rw [hM.symm]
        have p3:x (φ (N⊔M)) ∈ Im(x,{l | M ≤ l}) := by 
          simp; refine' ⟨φ (N⊔M),_,rfl ⟩ 
          calc 
            M ≤ N ⊔ M := by simp
            _ ≤ φ (N ⊔ M) :=subSequenceIndexGeOrig h1 _
        replace p3:=supIsUpperBound p3
        calc 
          ↑ r ≤ _ := (hN (by simp:N≤ (N ⊔ M))).le
          _ ≤ SUP (Im(x,{l | M ≤ l})) := p3
      exact infIsGreatestLowerBound p2
    set li:=limsup x  
    match li with
    | +∞ => simp
    | -∞ => simp at p1
    | (r:Real) =>
      replace p1:= EReal.coe_le_coe_iff.mp (p1 (r+1))
      simp at p1
      replace p1:=calc
        0 < 1 := by simp
        _ ≤ _ := p1
      simp at p1
  | (r:Real) =>
    by_contra hc; push_neg at hc
    set li:=limsup x with HH
    match li with
    | +∞ => simp at hc
    | -∞ =>
      simp only [sequenceN.convergesTo] at h2
      let nb:neighb (↑r:EReal) :={
        set:={e:EReal|r-1<e ∧ e<r+1}
        property:= by
          refine' ⟨_,by simp ⟩ 
          have p1:r - 1 < r := by simp
          have p2:r<r+1 := by simp
          exact ⟨EReal.coe_lt_coe_iff.mpr p1,EReal.coe_lt_coe_iff.mpr p2 ⟩ }
      refine' Exists.elim (h2 nb) _
      intro N hN; rw [limsup] at HH
      let p1:=notBoundedBelowIff.mpr HH.symm; simp [boundedBelow] at p1
      refine' Exists.elim (p1 (r-1))  _
      intro N2 hN2
      have p2:(x (φ (N2 ⊔ N))) ∈ Im(x,{l | N2 ≤ l}) := by 
        rw [mem_image]; refine' ⟨(φ (N2 ⊔ N)),_ ⟩ 
        simp; calc
          N2 ≤ N2 ⊔ N := by simp
          _ ≤ φ (N2 ⊔ N) := subSequenceIndexGeOrig h1 _
      replace p2:=supIsUpperBound p2
      replace hN:=hN (by simp :N≤ (N2 ⊔  N))
      simp at hN
      let p3:= calc
        _ ≤ _ :=p2
        _ < _ :=hN2
        _ = ↑(r - 1) := by simp
        _ < x (φ (N2 ⊔ N)) := hN.left
      simp at p3
    | (r':Real) =>
      simp at hc
      have p1:0<(r- r') / 2:= by
        exact div_pos (by simp [hc]) (by simp)
      simp only [sequenceN.convergesTo] at h2
      let nb:neighb (↑r:EReal) :={
        set:={e:EReal|↑(r - (r-r')/2)<e ∧e< ↑(r+ (r-r')/2)}
        property:= by
          refine' ⟨_,by simp ⟩ 
          simp only [mem_def,setOf]
          have p2:(r - (r - r') / 2) < r := by 
            simp [p1]; 
          have p3: r< (r+ (r-r')/2) := by
            simp [p1]; 
          exact ⟨EReal.coe_lt_coe_iff.mpr p2,EReal.coe_lt_coe_iff.mpr p3 ⟩ } 
      refine' Exists.elim (h2 nb) _
      intro N1 hN1; rw [limsup] at HH
      have p2: ∀ {y : EReal}, y ∈ Im(fun n => SUP (Im(x,{l | n ≤ l})),univ) → ↑(r- (r-r')/2)≤y:= by
        intro y hy
        refine' Exists.elim hy _
        intro N2 hN2; simp at hN2
        replace hN1:=hN1 (by simp:N1 ≤ N1⊔N2 ); simp only [mem_def,setOf] at hN1
        have p3:(x ∘ φ) (N1 ⊔ N2) ∈  Im(x,{l | N2 ≤ l}) := by
          simp; refine' ⟨φ (N1 ⊔ N2),_,rfl ⟩ 
          calc
            N2 ≤ N1 ⊔ N2 := by simp
            N1 ⊔ N2 ≤ φ (N1 ⊔ N2) :=subSequenceIndexGeOrig h1 _
        replace p3:=supIsUpperBound p3
        calc
          _ ≤ _ := hN1.left.le
          _ ≤ _ := p3
          _ = _ :=hN2
      replace p2:=infIsGreatestLowerBound p2; rw [HH.symm] at p2
      replace p2:=addLeAddMpr (EReal.coe_le_coe_iff.mp p2) (-r'); 
      rw [← sub_eq_add_neg,← sub_eq_add_neg,sub_self] at p2;
      have p3:=calc
        0 = _ := by simp
        _ < _:= p1
        _ = _  :=by ring
        _ ≤ 0 :=p2
      simp at p3

lemma liminfLeLimsup {x:sequenceN EReal}:liminf x ≤ limsup x := by
  rw [liminf,limsup]
  refine' infIsGreatestLowerBound _
  intro y hy
  refine' supIsLeastUpperBound _
  intro z hz
  refine' Exists.elim hy _
  intro Ny hNy
  refine' Exists.elim hz _
  intro Nz hNz
  simp at hNy hNz
  by_cases c: Ny≤ Nz
  · have p1:SUP (Im(x,{l | Nz ≤ l})) ≤ y := by
      rw [hNy.symm]
      refine' supMono _
      intro a ha; simp; 
      refine' Exists.elim ha _
      intro N hN; simp at hN
      exact ⟨_,le_trans c hN.left,hN.right ⟩ 
    calc 
      _ = _ :=hNz.symm
      _ ≤ SUP (Im(x,{l | Nz ≤ l})) :=INFleSUP ⟨x Nz,Nz,by simp ⟩
      _ ≤ _ :=p1
  · push_neg at c
    have p1:z ≤  INF (Im(x,{l | Ny ≤ l})) := by
      rw [hNz.symm]
      refine' infMono _
      intro a ha; simp;
      refine' Exists.elim ha _
      intro N hN; simp at hN
      exact ⟨_,le_trans c.le hN.left,hN.right ⟩
    calc
      _ ≤ _ := p1
      _ ≤ SUP (Im(x,{l | Ny ≤ l})) := INFleSUP ⟨x Ny,Ny,by simp ⟩
      _ = _ := hNy

lemma convergesToLIM {x:sequenceN EReal} (x0:LIM x):x.convergesTo x0.val:= by
  set X:=x0.val with HH
  match X with
  | +∞ =>
    let p1:=x0.liminf_eq_val; rw [liminf,HH.symm] at p1
    replace p1:=supEqPosInftyIff.mp p1
    refine' convergesToPosInftyIff.mpr _
    intro r
    refine' Exists.elim (p1 r) _
    intro a ha
    refine' Exists.elim (ha.left) _
    intro N hN
    refine' ⟨N,_ ⟩ 
    intro n hn
    have p2: a ≤ (fun n => INF (Im(x,{l | n ≤ l}))) n  := by
      rw [hN.right.symm];simp; refine' infMono _
      intro z hz; simp ;simp at hz
      refine' Exists.elim hz _
      intro N' hN'; refine' ⟨N',le_trans hn hN'.left,hN'.right ⟩ 
    have p3:(fun n => INF (Im(x,{l | n ≤ l}))) n ≤ x n :=by
      simp; refine' infIsLowerBound _
      simp; exact ⟨n,by simp ⟩ 
    calc
      _ < _ :=ha.right
      _ ≤  _ := p2
      _ ≤ _ :=p3
  | -∞ =>
    let p1:=x0.limsup_eq_val; rw [limsup,HH.symm] at p1
    replace p1:=infEqNegInftyIff.mp p1
    refine' convergesToNegInftyIff.mpr _
    intro r
    refine' Exists.elim (p1 r) _
    intro a ha
    refine' Exists.elim (ha.left) _
    intro N hN
    refine' ⟨N,_ ⟩ 
    intro n hn
    have p2:  (fun n => SUP (Im(x,{l | n ≤ l}))) n ≤ a  := by
      rw [hN.right.symm];simp; refine' supMono _
      intro z hz; simp ;simp at hz
      refine' Exists.elim hz _
      intro N' hN'; refine' ⟨N',le_trans hn hN'.left,hN'.right ⟩ 
    have p3:x n ≤ (fun n => SUP (Im(x,{l | n ≤ l}))) n  :=by
      simp; refine' supIsUpperBound _
      simp; exact ⟨n,by simp ⟩ 
    calc
      _ ≤  _ :=p3
      _ ≤  _ := p2
      _ < _ :=ha.right
  | (X':Real) =>
    refine' convergesToRealInERealIff.mpr _
    intro ε hε 
    let p1:=(infCloseEnough (HH.symm ▸ x0.limsup_eq_val) ) hε 
    let p2:=(supCloseEnough (HH.symm ▸ x0.liminf_eq_val) ) hε
    refine' Exists.elim p1 _
    intro a ha
    refine' Exists.elim p2 _
    intro b hb
    refine' Exists.elim ha.left _
    intro Na hNa
    refine' Exists.elim hb.left _
    intro Nb hNb
    refine' ⟨Na⊔Nb,_ ⟩ 
    intro n hn
    let p3:=x0.liminf_eq_val; rw [liminf] at p3
    let p4:=x0.limsup_eq_val; rw [limsup] at p4
    rw [p3,HH.symm] at hb; rw [p4,HH.symm] at ha
    have p5:↑b ≤ x n := by
      rw [hNb.right.symm]; simp
      refine' infIsLowerBound _
      refine' ⟨n,_,rfl ⟩ 
      calc 
        Nb ≤ Na ⊔ Nb := by simp
        _ ≤ _ :=hn
    have p6: x n ≤ ↑a := by
      rw [hNa.right.symm]; simp
      refine' supIsUpperBound _
      refine' ⟨n,_,rfl ⟩ 
      calc 
        Na ≤ Na ⊔ Nb := by simp
        _ ≤ _ :=hn
    have p7: (↑(X' - ε):EReal) < ↑ b := by
      refine' EReal.coe_lt_coe_iff.mpr _
      rw [sub_eq_add_neg];simp;exact EReal.coe_lt_coe_iff.mp hb.right
    have p8: ↑ a <  (↑(X' + ε):EReal) := by
      refine' EReal.coe_lt_coe_iff.mpr _
      let p9:=EReal.coe_lt_coe_iff.mp ha.right; rw [sub_eq_add_neg] at p9;simp at p9
      exact p9
    replace p7:=calc 
      _ < _ := p7
      _ ≤ _ := p5
    replace p8:=calc
      _ ≤ _ := p6
      _ < _ := p8
    exact ⟨p7,p8 ⟩ 

instance: HausdorffSpace EReal := by
  have p1:(∀ {x y : EReal}, x ≠ y → ∃ (u1:neighb x)(u2:neighb y), u1.set ∩ u2.set = ∅) := by
    intro x y hxy
    match x with
    | -∞ =>
      match y with
      | -∞ => simp at hxy
      | +∞ =>
        let u1:neighb (-∞) := {
          set:={r:EReal|r<0}
          property:=by simp }
        let u2:neighb (+∞) := {
          set:={r:EReal|0<r}
          property:=by simp }
        refine' ⟨u1,u2,_ ⟩ 
        simp;by_contra hc 
        replace hc:=setNonemptyIff.mpr hc
        refine' Exists.elim hc _
        intro a ha; simp at ha
        replace ha:=calc
          _ < _ := ha.left
          _ < _ := ha.right
        simp at ha
      | (y':Real) =>
        let u1:neighb (-∞) := {
          set:={r:EReal|r<↑ (y'-1)}
          property:=by 
            refine' ⟨_,by simp ⟩ 
            simp only [mem_def,setOf]; 
            exact EReal.bot_lt_coe _}
        let u2:neighb (y':EReal) := {
          set:={r:EReal|↑(y'-1)<r ∧ r< ↑(y'+1)}
          property:=by 
            refine' ⟨_,by simp ⟩
            simp only [mem_def,setOf];
            have p1: (y' - 1) < y' := by simp
            have p2: y'<y'+1 := by simp
            exact ⟨EReal.coe_lt_coe_iff.mpr p1, EReal.coe_lt_coe_iff.mpr p2 ⟩  }
        refine' ⟨u1,u2,_ ⟩ 
        simp;by_contra hc 
        replace hc:=setNonemptyIff.mpr hc
        refine' Exists.elim hc _
        intro a ha; simp at ha
        replace ha:=calc
          _ < _ := ha.left
          _ < _ := ha.right.left
        simp at ha
    | +∞ => 
      match y with
      | +∞ => simp at hxy
      | -∞ =>
        let u1:neighb (+∞) := {
          set:={r:EReal|0<r}
          property:=by simp }
        let u2:neighb (-∞) := {
          set:={r:EReal|r<0}
          property:=by simp }
        refine' ⟨u1,u2,_ ⟩ 
        simp;by_contra hc 
        replace hc:=setNonemptyIff.mpr hc
        refine' Exists.elim hc _
        intro a ha; simp at ha
        replace ha:=calc
          _ < _ := ha.left
          _ < _ := ha.right
        simp at ha
      | (y':Real) =>
        let u1:neighb (+∞) := {
          set:={r:EReal|↑ (y'+1)<r}
          property:=by 
            refine' ⟨_,by simp ⟩ 
            simp only [mem_def,setOf]; 
            exact EReal.coe_lt_top _}
        let u2:neighb (y':EReal) := {
          set:={r:EReal|↑(y'-1)<r ∧ r< ↑(y'+1)}
          property:=by 
            refine' ⟨_,by simp ⟩
            simp only [mem_def,setOf];
            have p1: (y' - 1) < y' := by simp
            have p2: y'<y'+1 := by simp
            exact ⟨EReal.coe_lt_coe_iff.mpr p1, EReal.coe_lt_coe_iff.mpr p2 ⟩  }
        refine' ⟨u1,u2,_ ⟩ 
        simp;by_contra hc 
        replace hc:=setNonemptyIff.mpr hc
        refine' Exists.elim hc _
        intro a ha; simp at ha
        replace ha:=calc
          _ < _ := ha.right.right
          _ < _ := ha.left
        simp at ha
    | (x':Real) =>
      match y with
      | -∞ =>
        let u1:neighb (↑x':EReal) := {
          set:={r:EReal|↑(x'-1)<r ∧ r< ↑(x'+1)}
          property:=by 
            refine' ⟨_,by simp ⟩
            simp only [mem_def,setOf];
            have p1: (x' - 1) < x' := by simp
            have p2: x'<x'+1 := by simp
            exact ⟨EReal.coe_lt_coe_iff.mpr p1, EReal.coe_lt_coe_iff.mpr p2 ⟩  }
        let u2:neighb (-∞ ):= {
          set:={r:EReal|r<↑ (x'-1)}
          property:=by 
            refine' ⟨_,by simp ⟩ 
            simp only [mem_def,setOf]; 
            exact EReal.bot_lt_coe _}
        refine' ⟨u1,u2,_ ⟩ 
        simp;by_contra hc 
        replace hc:=setNonemptyIff.mpr hc
        refine' Exists.elim hc _
        intro a ha; simp at ha
        replace ha:=calc
          _ < _ := ha.right
          _ < _ := ha.left.left
        simp at ha
      | +∞ =>
        let u1:neighb (↑x':EReal) := {
          set:={r:EReal|↑(x'-1)<r ∧ r< ↑(x'+1)}
          property:=by 
            refine' ⟨_,by simp ⟩
            simp only [mem_def,setOf];
            have p1: (x' - 1) < x' := by simp
            have p2: x'<x'+1 := by simp
            exact ⟨EReal.coe_lt_coe_iff.mpr p1, EReal.coe_lt_coe_iff.mpr p2 ⟩  }
        let u2:neighb (+∞ ):= {
          set:={r:EReal|↑ (x'+1)<r}
          property:=by 
            refine' ⟨_,by simp ⟩ 
            simp only [mem_def,setOf]; 
            exact EReal.coe_lt_top _}
        refine' ⟨u1,u2,_ ⟩ 
        simp;by_contra hc 
        replace hc:=setNonemptyIff.mpr hc
        refine' Exists.elim hc _
        intro a ha; simp at ha
        replace ha:=calc
          _ < _ := ha.left.right
          _ < _ := ha.right
        simp at ha
      | (y':Real) =>
        simp at hxy
        have p0 : 0< |x'-y'| := by
          simp;by_contra hc; replace hc:=congrArg (.+y') hc
          simp at hc; exact hxy hc
        let u1:neighb (↑x':EReal) := {
          set:={r:EReal|↑(x'-|x'-y'|/2)<r ∧ r< ↑(x'+|x'-y'|/2)}
          property:=by 
            refine' ⟨_,by simp ⟩
            simp only [mem_def,setOf];
            have p1: (x' - abs (x' - y') / 2) < x' := by 
              simp;exact div_pos p0 (by simp)
            have p2:x'<(x' + abs (x' - y') / 2) := by
              simp; exact div_pos p0 (by simp)
            exact ⟨EReal.coe_lt_coe_iff.mpr p1, EReal.coe_lt_coe_iff.mpr p2 ⟩  }
        let u2:neighb (↑y':EReal) :={
          set:={r:EReal|↑(y'-|x'-y'|/2)<r ∧ r< ↑(y'+|x'-y'|/2)}
          property:=by 
            refine' ⟨_,by simp ⟩
            simp only [mem_def,setOf];
            have p1: (y' - abs (x' - y') / 2) < y' := by 
              simp;exact div_pos p0 (by simp)
            have p2:y'<(y' + abs (x' - y') / 2) := by
              simp; exact div_pos p0 (by simp)
            exact ⟨EReal.coe_lt_coe_iff.mpr p1, EReal.coe_lt_coe_iff.mpr p2 ⟩  }
        refine' ⟨u1,u2,_ ⟩ 
        simp;by_contra hc 
        replace hc:=setNonemptyIff.mpr hc
        refine' Exists.elim hc _
        intro a ha; 
        match a with
        | +∞ =>simp at ha
        | -∞ =>simp at ha
        | (a':Real) =>
          simp at ha
          rw [← EReal.coe_sub,← EReal.coe_sub,← EReal.coe_add,← EReal.coe_add] at ha
          simp only [EReal.coe_lt_coe_iff] at ha
          have p1':|x'-a'|< |x'-y'|/2 := by
            refine' abs_sub_lt_iff.mpr _
            let p2:=addLtAddMpr (ha.left.left) ( abs (x' - y') / 2 -a')
            have p3: x' - abs (x' - y') / 2 + (abs (x' - y') / 2 - a') = x'-a' := by abel
            have p4: a' + (abs (x' - y') / 2 - a') = abs (x' - y') / 2 := by abel
            rw [p3,p4] at p2; 
            let p5:=addLtAddMpr (ha.left.right) (-x')
            rw [← sub_eq_add_neg] at p5; simp at p5
            exact ⟨p2,p5⟩ 
          have p2': |y'-a'|< |x'-y'|/2 := by
            refine' abs_sub_lt_iff.mpr _
            let p2:=addLtAddMpr (ha.right.left) ( abs (x' - y') / 2 -a')
            have p3:y' - abs (x' - y') / 2 + (abs (x' - y') / 2 - a')  = y'-a' :=by abel
            have p4:a' + (abs (x' - y') / 2 - a')= abs (x' - y') / 2:= by abel
            rw [p3,p4] at p2
            let p5:=addLtAddMpr (ha.right.right) (-y')
            rw [← sub_eq_add_neg] at p5; simp at p5
            exact ⟨p2,p5⟩ 
          have p3:|y'-a'| = |a'-y'|  := abs_sub_comm _ _
          rw [p3] at p2'; replace p3:=abs_add (x' - a') (a' - y')
          have p4:(x' - a' + (a' - y')) = x'-y':= by abel
          rw [p4] at p3
          replace p3:=calc
            _ ≤ _ :=p3
            _ < |x' - y'| / 2 + |a'-y'| :=addLtAddMpr p1' _
            _ = |a'-y'| + |x' - y'| / 2 := add_comm _ _
            _ < |x' - y'| / 2 + |x' - y'| / 2 := addLtAddMpr p2' _
            _ = |x' - y'| := by ring
          simp at p3
  exact ⟨p1⟩ 

@[simp]
lemma uniqueLIM {x:sequenceN EReal} {x0 x0':LIM x}: x0=x0' := by
  let p1:=limitUniqueInHausdorff (convergesToLIM x0) (convergesToLIM x0')
  calc 
    x0 = ⟨x0.val,_,_ ⟩ := rfl
    _ = ⟨x0'.val,_,_ ⟩ := by simp_rw [p1]

lemma leAnyPosEpsilon' {x y:ℝ}(h:∀{ε:ℝ},ε>0->x ≤ y+ε):x≤y := by
  by_contra hc; push_neg at hc
  have p1: 0<(x-y) := by simp [hc]
  have p2:=div_pos p1 (by simp:0<(2:Real))
  replace h:= addLeAddMpr (h p2) (-x); rw [← sub_eq_add_neg,sub_self] at h
  have p3: y + (x - y) / 2 + -x = - ((x-y)/2) := by ring
  rw [p3] at h;replace h:=leFlip h; rw [neg_neg] at h
  replace p3:=calc
    _ < _ := p2
    _ ≤ _ := h
  simp at p3

lemma geAnyNegEpsilon' {x y:ℝ}(h:∀{ε:ℝ},ε>0->x-ε ≤ y):x≤y := by
  have h' :∀{ε:ℝ},ε>0->x ≤ y+ε := by
    intro ε hε 
    let p1:=h hε ; simp at p1; exact p1
  exact leAnyPosEpsilon' h'

lemma leAnyPosEpsilon {x:EReal} {y:Real} (h:∀{ε:ℝ},ε>0->x ≤ y+ε):x≤y := by
  match x with
  | +∞ =>
    let p1:=h (by simp:(1:Real)>0);rw [← EReal.coe_add] at p1
    have p2:↑(y + 1) < +∞ :=EReal.coe_lt_top _
    replace p2:=calc
      _ ≤ _ := p1
      _ < _ := p2
    simp at p2
  | -∞ => simp
  | (x':ℝ ) =>
    have h':∀{ε:ℝ},ε>0->x' ≤ y+ε := by
      intro ε hε ;
      replace h:=h hε ; rw [← EReal.coe_add,EReal.coe_le_coe_iff] at h;
      exact h
    rw [EReal.coe_le_coe_iff]; exact leAnyPosEpsilon'  h'

lemma  geAnyNegEpsilon {y:EReal} {x:Real} (h:∀{ε:ℝ},ε>0->x-ε ≤ y):x≤y := by
  match y with
  | -∞ =>
    let p1:=h (by simp:(1:Real)>0);rw [← EReal.coe_sub] at p1
    have p2:-∞ < ↑(x - 1) :=EReal.bot_lt_coe _
    replace p2:=calc
      _ ≤ _ := p1
      _ < _ := p2
    simp at p2
  | +∞ => simp
  | (y':ℝ ) =>
    have h':∀{ε:ℝ},ε>0->x-ε ≤ y' := by
      intro ε hε ;
      replace h:=h hε ; rw [← EReal.coe_sub,EReal.coe_le_coe_iff] at h;
      exact h
    rw [EReal.coe_le_coe_iff]; exact geAnyNegEpsilon'  h'

lemma convergenceImpliesLIM {x:sequenceN EReal}(h:x.convergesTo x0):∃x0':LIM x,x0'=x0 := by 
  match x0 with
  | +∞ =>
    replace h:=convergesToPosInftyIff.mp h
    have p1: liminf x = +∞ := by
      rw [liminf];refine' supEqPosInftyIff.mpr _
      intro r ; refine' Exists.elim (h (r+1)) _
      intro N hN; refine' ⟨INF (Im(x,{l | N ≤ l})),_ ⟩ ;simp
      have p2: ∀{z:EReal}, z∈ Im(x,{l | N ≤ l}) -> ↑(r+1 )≤ z := by
        intro z hz; simp at hz
        refine' Exists.elim hz _
        intro zN hzN; rw [hzN.right.symm]; exact (hN hzN.left).le
      replace p2:=infIsGreatestLowerBound p2
      calc 
        (↑r:EReal) < ↑ (r+1) := by refine' EReal.coe_lt_coe_iff.mpr _;simp
        _ ≤ _ := p2
    have p2:=p1 ▸ liminfLeLimsup; simp at p2
    exact ⟨⟨_,p2,p1 ⟩ ,rfl ⟩ 
  | -∞ =>
    replace h:=convergesToNegInftyIff.mp h
    have p1: limsup x = -∞ := by
      rw [limsup];refine' infEqNegInftyIff.mpr _
      intro r ; refine' Exists.elim (h (r-1)) _
      intro N hN; refine' ⟨SUP (Im(x,{l | N ≤ l})),_ ⟩ ;simp
      have p2: ∀{z:EReal}, z∈ Im(x,{l | N ≤ l}) -> z≤ ↑ (r-1) := by
        intro z hz; simp at hz
        refine' Exists.elim hz _
        intro zN hzN; rw [hzN.right.symm]; exact (hN hzN.left).le
      replace p2:=supIsLeastUpperBound p2
      calc 
        _ ≤ _ := p2
        (r-1)< (↑r:EReal) := by refine' EReal.coe_lt_coe_iff.mpr _;simp
    have p2:=p1 ▸ liminfLeLimsup; simp at p2
    exact ⟨⟨_,p1,p2 ⟩ ,rfl ⟩ 
  | (x0':ℝ) =>
    have p1:limsup x ≤  x0' := by
      refine' leAnyPosEpsilon _
      intro ε hε ;rw [convergesToRealInERealIff] at h
      refine' Exists.elim (h hε) _
      intro N hN; rw [limsup]
      have p2: SUP (Im(x,{l | N ≤ l})) ≤ ↑x0' + ↑ε := by
        refine' supIsLeastUpperBound _
        intro a ha; 
        refine' Exists.elim ha _
        intro Na hNa; rw [hNa.right.symm]
        exact (hN hNa.left).right.le
      have p3: SUP (Im(x,{l | N ≤ l})) ∈  (Im(fun n => SUP (Im(x,{l | n ≤ l})),univ)) := by simp
      replace p3:=infIsLowerBound p3
      exact le_trans p3 p2
    have p2:x0' ≤ liminf x := by
      refine' geAnyNegEpsilon _
      intro ε hε ;rw [convergesToRealInERealIff] at h
      refine' Exists.elim (h hε) _
      intro N hN; rw [liminf]
      have p2:↑x0' - ↑ε ≤ INF (Im(x,{l | N ≤ l}))  := by
        refine' infIsGreatestLowerBound _
        intro a ha; 
        refine' Exists.elim ha _
        intro Na hNa; rw [hNa.right.symm]
        rw [← EReal.coe_sub]
        exact (hN hNa.left).left.le
      have p3: INF (Im(x,{l | N ≤ l})) ∈  (Im(fun n => INF (Im(x,{l | n ≤ l})),univ)) := by simp
      replace p3:=supIsUpperBound p3
      exact le_trans  p2 p3
    have p3:= calc
      _ ≤ _ := liminfLeLimsup
      _ ≤ _ := p1
    have p4:= calc
      _ ≤ _ := p2 
      _ ≤ _ := liminfLeLimsup
    let l:LIM x := ⟨_,le_antisymm p1 p4,le_antisymm p3 p2 ⟩ 
    refine' ⟨l,rfl ⟩ 

theorem squeezeTheorem' {x y z:sequenceN ℝ}{z0:ℝ}(h1:x.convergesTo z0)(h2:y.convergesTo z0)
(h3:∀(n:ℕ),x n ≤ z n ∧ z n ≤ y n):z.convergesTo z0 := by
  refine' convergesInRealIff.mpr _
  intro ε hε 
  let p2:=(convergesInRealIff.mp h1) hε 
  let p3:=(convergesInRealIff.mp h2) hε 
  refine' Exists.elim p2 _
  intro Nx hx
  refine' Exists.elim p3 _
  intro Ny hy
  refine' ⟨Nx⊔Ny,_ ⟩ 
  intro n hn; simp at hn
  by_cases c:z n - z0 >0
  case neg=>
    push_neg at c
    rw [abs_of_nonpos c]
    replace hx:=abs_lt.mp (hx hn.left)
    have p4:x n - z0 ≤ z n - z0 := by 
      simp; exact (h3 n).left
    replace p4:= calc
      _ < _ :=hx.left
      _ ≤ _ := p4
    simp; replace p4:=ltFlip p4; simp at p4
    exact p4
  case pos =>
    rw [abs_of_pos c]
    replace hy:=abs_lt.mp (hy hn.right)    
    have p4:z n - z0 ≤ y n - z0 := by 
      simp; exact (h3 n).right
    replace p4:= calc
      _ ≤ _ := p4
      _ < _ := hy.right
    exact p4

theorem squeezeTheorem  {x y z:sequenceN EReal}{z0:EReal}(h1:x.convergesTo z0)(h2:y.convergesTo z0)
(h3:∀(n:ℕ),x n ≤ z n ∧ z n ≤ y n):z.convergesTo z0 := by
  have p1: liminf x ≤ liminf z := by
    refine' supIsLeastUpperBound _
    intro a ha; simp at ha
    refine' Exists.elim ha _
    intro n hn
    have p2:INF (Im(x,{l | n ≤ l})) ≤ INF (Im(z,{l | n ≤ l})) := by
      refine' infIsGreatestLowerBound _
      intro b hb; simp at hb
      refine' Exists.elim hb _
      intro n2 hn2
      have p3:x n2 ∈ Im(x,{l | n ≤ l}) := by
        simp; exact ⟨n2,hn2.left,rfl ⟩ 
      calc
        _ ≤ _ := infIsLowerBound p3
        _ ≤ _ := (h3 n2).left
        _ = _ := hn2.right
    have p3:INF (Im(z,{l | n ≤ l})) ∈  Im(fun n => INF (Im(z,{l | n ≤ l})),univ) :=by
      simp
    calc
      _ = _ := hn.symm
      _ ≤ _ := p2
      _ ≤ _ := supIsUpperBound p3
  have p2: limsup z ≤ limsup y := by
    refine' infIsGreatestLowerBound _
    intro a ha; simp at ha
    refine' Exists.elim ha _
    intro n hn
    have p2: SUP (Im(z,{l | n ≤ l})) ≤ SUP (Im(y,{l | n ≤ l}))  := by
      refine' supIsLeastUpperBound _
      intro b hb; simp at hb
      refine' Exists.elim hb _
      intro n2 hn2
      have p3:y n2 ∈ Im(y,{l | n ≤ l}) := by
        simp; exact ⟨n2,hn2.left,rfl ⟩ 
      calc
        _ = _ := hn2.right.symm
        _ ≤ _ := (h3 n2).right
        _ ≤ _ := supIsUpperBound p3
    have p3:SUP (Im(z,{l | n ≤ l})) ∈  Im(fun n => SUP (Im(z,{l | n ≤ l})),univ) :=by
      simp
    calc
      _ ≤ _ := infIsLowerBound p3
      _ ≤ _ := p2
      _ = _ := hn
  let p3:=convergenceImpliesLIM h1
  let p4:=convergenceImpliesLIM h2
  refine' Exists.elim p3 _
  intro lim1 hlim1
  refine' Exists.elim p4 _
  intro lim2 hlim2
  rw [(lim1.liminf_eq_val).symm] at hlim1
  rw [hlim1] at p1
  rw [(lim2.limsup_eq_val).symm] at hlim2
  rw [hlim2] at p2
  let lim3:LIM z :=⟨_,
    le_antisymm p2 (le_trans p1 (liminfLeLimsup)),
    le_antisymm (le_trans (liminfLeLimsup) p2) p1 ⟩ 
  exact convergesToLIM lim3

theorem monoConvergenceIncreasing' {x:sequenceN ℝ}(h1:Monotone x) (h2:∃M:ℝ, ∀{a:ℝ},a∈Im(x,univ)-> a≤M):
∃x0:ℝ ,x.convergesTo x0 := by
  rw [Monotone] at h1
  refine' Exists.elim h2 _
  intro M hM
  set M':=SUP (Im(fun n=>↑(x n),univ)) with HH
  match M' with
  | -∞ =>
    have p1: ((x 0):EReal) ∈ (Im(fun n=>↑(x n),univ)) := by simp
    replace p1:=supIsUpperBound p1; rw [HH.symm] at p1; simp at p1
  | +∞ =>
    have p1:∀ {a : EReal}, a ∈ (Im(fun n=>↑(x n),univ)) → a ≤ M := by
      intro a ha; simp at ha
      refine' Exists.elim ha _
      intro N2 hN2; rw [hN2.symm]; simp
      exact hM (by simp)
    replace p1:=supIsLeastUpperBound p1
    rw [HH.symm] at p1; simp at p1
  | (M'':Real) =>
    refine' ⟨M'',convergesInRealIff.mpr _ ⟩ 
    intro ε hε 
    let p1:=supCloseEnough HH.symm hε 
    refine' Exists.elim p1 _
    intro a ha; let p2:=ha.left; simp at p2
    refine' Exists.elim p2 _
    intro N hN
    refine' ⟨N,_ ⟩ 
    intro n hn; let p3:=ha.right; rw [HH.symm] at p3
    rw [EReal.coe_lt_coe_iff] at p3
    have p4: ↑ ((x n):EReal) ∈  Im(fun n => ↑(x n),univ) := by simp
    replace p4:=supIsUpperBound p4; rw [HH.symm] at p4; simp at p4
    rw [abs_of_nonpos (by simp [p4])]; simp
    replace p3:=calc
      _ < _ := p3
      _ ≤  (x N) + ε := by rw [hN.symm]
      _ ≤ (x n) + ε := by simp; exact  h1 hn
    replace p3:=addLtAddMpr p3 (- x n)
    rw [← sub_eq_add_neg] at p3; simp at p3; exact p3

theorem monoConvergenceDecreasing' {x:sequenceN ℝ}(h1:Monotone fun n=>-x n) 
(h2:∃M:ℝ, ∀{a:ℝ},a∈Im(x,univ)-> M≤a): ∃x0:ℝ ,x.convergesTo x0 := by
  have p2':∃M':ℝ, ∀{a:ℝ},a∈Im((fun n=>-x n),univ)-> a ≤ M' := by
    refine' Exists.elim h2 _
    intro MM hMM; refine' ⟨-MM,_ ⟩ 
    intro a ha; 
    have p3: - a ∈ Im(x,univ) := by
      simp; simp at ha
      refine' Exists.elim ha _
      intro N hN
      refine' ⟨N,_ ⟩ 
      replace hN:=congrArg (-.) hN
      simp at hN; exact hN
    replace p3:= leFlip (hMM p3); 
    simp at p3; exact p3
  let p3:= monoConvergenceIncreasing' h1 p2'
  refine' Exists.elim p3 _
  intro x0 hx0
  refine' ⟨-x0,convergesInRealIff.mpr _ ⟩ 
  rw [convergesInRealIff] at hx0
  intro ε hε 
  refine' Exists.elim (hx0 hε ) _
  intro N hN
  refine' ⟨N,_ ⟩ 
  intro n hn; replace hN:=hN hn
  have p4: -(x n - -x0) = (-x n - x0 ) := by abel
  rw [p4.symm] at hN;rw [abs_neg] at hN
  exact hN

theorem monoConvergence {x:sequenceN EReal} (h:Monotone x):  LIM x := by
  set M := SUP (Im(x,univ)) with HH
  match M with
  | -∞ =>
    have p1: ∀{a}, a∈ Im(x,univ) -> a=-∞ := by
      intro a ha
      replace ha:=supIsUpperBound ha
      rw [HH.symm] at ha; simp at ha; exact ha
    have p2:limsup x ≤ -∞ := by
      rw [limsup]; refine' infIsLowerBound _
      simp; refine' ⟨0,_ ⟩ 
      have p3:SUP (Im(x,{l | 0 ≤ l})) ≤  ⊥ := by
        refine' supIsLeastUpperBound _
        intro y hy; simp at hy
        refine' Exists.elim hy _
        intro NN hNN; rw [hNN.symm]
        have p4:x NN ∈  Im(x,univ)  := by simp
        rw [p1 p4]
      rw [le_bot_iff] at p3
      exact p3
    exact ⟨_,le_bot_iff.mp p2,le_bot_iff.mp (le_trans liminfLeLimsup p2) ⟩ 
  | +∞ =>
    have p1: x.convergesTo (+∞) := by
      rw [convergesToPosInftyIff]
      intro l
      refine' Exists.elim (supEqPosInftyIff.mp (HH.symm) l) _
      intro a ha
      refine' Exists.elim (ha.left) _
      intro N hN
      refine' ⟨N,_ ⟩ 
      intro n hn
      calc
        _ < _ := ha.right
        _ = _  := hN.right.symm
        _ ≤ _ :=h hn
    exact choose (convergenceImpliesLIM p1)
  | (M':Real) =>
    have p1: limsup x ≤ M' := by
      rw [limsup]; refine' infIsLowerBound _
      refine' ⟨0,_ ⟩ ; simp; simp at HH
      exact HH.symm
    have p2: M' ≤ liminf x := by
      refine' geAnyNegEpsilon _
      intro ε hε ; rw [liminf]
      refine' Exists.elim  (supCloseEnough HH.symm (div_pos hε (by simp:(0:ℝ)<2 ))) _
      intro a ha
      refine' Exists.elim (ha.left) _
      intro N hN; rw [HH.symm] at ha
      have p3:INF (Im(x,{l | N ≤ l})) ∈  Im(fun n => INF (Im(x,{l | n ≤ l})),univ) := by simp
      have p4:  ↑(a - ε/2) ≤  INF (Im(x,{l | N ≤ l}))   := by
        refine' infIsGreatestLowerBound _
        intro z hz; refine' Exists.elim  hz _
        intro NN hNN; simp at hNN
        let p5:=h hNN.left
        rw [hNN.right.symm]; refine' le_trans _ p5
        rw [hN.right,EReal.coe_le_coe_iff];
        simp [(div_pos  hε (by simp:(0:ℝ)<2 )).le]
      replace p3:=supIsUpperBound p3
      refine' le_trans _ p3; refine' le_trans _ p4
      rw [←EReal.coe_sub,EReal.coe_le_coe_iff]; 
      rw [EReal.coe_lt_coe_iff] at ha; simp
      have p5: a - ε / 2 + ε = a + ε / 2 := by ring
      rw [p5]; exact ha.right.le
    exact ⟨_, le_antisymm p1 (le_trans p2 liminfLeLimsup),le_antisymm (le_trans liminfLeLimsup p1) p2⟩ 

lemma convergentInRealIsBounded {x:sequenceN ℝ} {x0:ℝ} (h1:x.convergesTo x0):
∃M:ℝ,∀{y},y∈Im(x,univ)-> |y| < M := by
  refine' Exists.elim (convergesInRealIff.mp h1 (by simp:0<(1:Real))) _
  intro N hN
  match N with
  | 0 =>
    refine' ⟨|x0|+1,_ ⟩ 
    intro y hy; refine' Exists.elim hy _
    intro Ny hNy; have p1:=@hN Ny (by simp)
    rw [hNy.right.symm]
    replace p1:=leAddLt (by simp:|x0|≤|x0|) p1
    calc
      |x Ny| = |x0+((x Ny)-x0)| := by simp
      _ ≤  |x0| + |x Ny - x0| :=  abs_add _ _
      _ < _ := p1
  | .succ N' =>
    let L:=(List.range N'.succ).map (|x .|)
    let MM:=(L.mergeSort (.≥.))[0]
    refine' ⟨(MM+1)⊔(|x0|+1),_  ⟩ 
    intro y hy
    refine' Exists.elim hy _
    intro Ny hNy; rw [hNy.right.symm,lt_sup_iff]
    by_cases c1: N'.succ ≤ Ny
    case pos =>
      refine' Or.inr _
      have p3:=hN c1
      have p4:=leAddLt (by simp:|x0|≤|x0|) p3
      calc
        |x Ny| = |x0+((x Ny)-x0)| := by simp
        _ ≤  |x0| + |x Ny - x0| :=  abs_add _ _
        _ < _ := p4
    case neg =>
      refine' Or.inl _
      push_neg at c1
      have p1: Ny<L.length := by simp [c1]
      replace p2:=listGetIsMem p1
      by_cases c2:|x Ny| = MM
      · rw [c2]; simp
      · have p3:L[Ny] = |x Ny| := by simp; 
        rw [p3] at p2
        have p4:= (sortFirstIsMax (.≥.) L (by simp)) ((memSortIffMemOrig _ _).mpr p2) c2
        calc
          _ ≤ _ := p4
          _ < _ := by simp

lemma convergentAdd {x y:sequenceN ℝ}{x0 y0:ℝ}(h1:x.convergesTo x0)(h2:y.convergesTo y0):
sequenceN.convergesTo (fun n=>(x n)+(y n)) (x0+y0) := by
  rw [convergesInRealIff]
  intro ε hε 
  let p1:=div_pos hε (by simp:(0:ℝ)<2)
  refine' Exists.elim (convergesInRealIff.mp h1 p1) _
  intro Nx hNx
  refine' Exists.elim (convergesInRealIff.mp h2 p1) _
  intro Ny hNy
  refine' ⟨Nx⊔Ny,_ ⟩ 
  intro n hn; simp at hn
  calc
    |x n + y n - (x0 + y0)| = |(x n -x0)+(y n -y0)| := by refine' congrArg abs _;ring
    _ ≤ |(x n -x0)|+|(y n -y0)| := abs_add _ _
    _ < ε/2 + |(y n -y0)| := by simp [hNx hn.left]
    _ < ε/2 + ε/2 := leAddLt (by simp)  (hNy hn.right)
    _ = _ := by simp

lemma convergentTime {x y:sequenceN ℝ}{x0 y0:ℝ}(h1:x.convergesTo x0)(h2:y.convergesTo y0):
sequenceN.convergesTo (fun n=>(x n)*(y n)) (x0*y0) := by
  refine' convergesInRealIff.mpr _
  intro ε hε 
  let ε1:=(ε/(3*(1⊔|y0|))) ⊓ 1
  let ε2:=(ε/(3*(1⊔|x0|))) ⊓ 1
  have p1: 0<ε1 := by simp; exact div_pos hε (by simp)
  have p2: 0<ε2 := by simp; exact div_pos hε (by simp)
  refine' Exists.elim (convergesInRealIff.mp h1 p1) _
  intro Nx hNx
  refine' Exists.elim (convergesInRealIff.mp h2 p2) _
  intro Ny hNy
  refine' ⟨Nx⊔Ny,_ ⟩ 
  intro n hn
  simp at hn
  have p3': |(x n - x0) * y0| < ε / 3 := by
    rw [abs_mul]
    by_cases c1: y0 ≠ 0
    · have p4:=abs_pos.mpr c1
      replace p4:=mulPosLtMulPosMpr (hNx hn.left) p4
      have p5: ε1 * abs y0 ≤   ε / 3 := by 
        simp; rw [mul_comm _ (|y0|),realNonnegMulMinEqMinMulNonneg ( by simp:0≤ abs y0)]
        simp; refine' Or.inl _
        have p6: 3*|y0| ≤  (3 * (1 ⊔ |y0|)) := by simp
        replace p6:=mulNonNegLeMulNonMegMpr
          (mulNonNegLeMulNonMegMpr (invLeInvMpr (by simp [c1]) p6) (by simp:0≤|y0|)) hε.le
        have p7:1 / (3 * (1 ⊔ abs y0)) * abs y0 * ε = abs y0 * (ε / (3 * (1 ⊔ abs y0))) := by ring
        have p8:=calc
          1 / (3 * abs y0) * abs y0 * ε = (1/ abs y0)*( abs y0)*(ε/3)  := by ring
          _ = 1*(ε/3) := by refine' congrArg (.*(ε/3) ) (div_mul_cancel _ (by simp [c1]));
        rw [p7,p8] at p6; simp at p6; exact p6
      calc
        _ < _ := p4
        _ ≤ _ := p5
    · push_neg at c1
      rw [c1]; simp; exact div_pos hε (by simp)
  have p4': |(y n - y0) * x0| < ε / 3  := by
    rw [abs_mul]
    by_cases c1: x0 ≠ 0
    · have p4:=abs_pos.mpr c1
      replace p4:=mulPosLtMulPosMpr (hNy hn.right) p4
      have p5: ε2 * abs x0 ≤   ε / 3 := by 
        simp; rw [mul_comm _ (|x0|),realNonnegMulMinEqMinMulNonneg ( by simp:0≤ abs x0)]
        simp; refine' Or.inl _
        have p6: 3*|x0| ≤  (3 * (1 ⊔ |x0|)) := by simp
        replace p6:=mulNonNegLeMulNonMegMpr
          (mulNonNegLeMulNonMegMpr (invLeInvMpr (by simp [c1]) p6) (by simp:0≤|x0|)) hε.le
        have p7:1 / (3 * (1 ⊔ abs x0)) * abs x0 * ε = abs x0 * (ε / (3 * (1 ⊔ abs x0))) := by ring
        have p8:=calc
          1 / (3 * abs x0) * abs x0 * ε = (1/ abs x0)*( abs x0)*(ε/3)  := by ring
          _ = 1*(ε/3) := by refine' congrArg (.*(ε/3) ) (div_mul_cancel _ (by simp [c1]));
        rw [p7,p8] at p6; simp at p6; exact p6
      calc
        _ < _ := p4
        _ ≤ _ := p5
    · push_neg at c1
      rw [c1]; simp; exact div_pos hε (by simp)         
  have p5:=calc
    |x n * y n - x0 * y0| = |(x n-x0)*(y0)+(y n-y0)*(x n-x0)+(y n-y0)*x0| := by
                      refine' congrArg abs _; ring
    _ ≤ |(x n-x0)*(y0)+(y n-y0)*(x n-x0)|+|(y n-y0)*x0| := abs_add _ _
    _ ≤ |(x n-x0)*(y0)|+|(y n-y0)*(x n-x0)|+|(y n-y0)*x0| := by 
                      refine' addLeAddMpr _ (|(y n-y0)*x0|) ;exact abs_add _ _
    _ = |(x n-x0)*(y0)|+(|(y n-y0)*(x n-x0)|+|(y n-y0)*x0|) := add_assoc _ _ _
    _ < ε/3 + (|(y n-y0)*(x n-x0)|+|(y n-y0)*x0|) := by 
                      refine' addLtAddMpr _ (|(y n-y0)*(x n-x0)|+|(y n-y0)*x0|) ;exact p3'
    _ = |(y n-y0)*x0|+(|(y n-y0)*(x n-x0)|+ε/3) := by ring
    _ < ε/3 + (|(y n-y0)*(x n-x0)|+ε/3) := addLtAddMpr p4' _
  have p6: ε1 ≤ ε/3 := by 
    simp;refine' Or.inl _
    have p7: 1 / (3 * (1 ⊔ abs y0)) ≤ 1 / 3 := invLeInvMpr (by simp) (by simp)
    calc
      ε / (3 * (1 ⊔ abs y0))  = (1 / (3 * (1 ⊔ abs y0)))*ε := by ring
      _ ≤ (1 / 3)*ε := mulNonNegLeMulNonMegMpr p7 hε.le
      _ = _ :=by ring
  have p7:= calc
    |(y n - y0) * (x n - x0)| = (|y n - y0|)*(|x n - x0|) := abs_mul  _ _
    _ ≤ 1*(|x n - x0|) := by 
                refine' mulNonNegLeMulNonMegMpr (le_trans (hNy hn.right).le (by simp)) (by simp)
    _ = |x n - x0| := by simp
    _ ≤  ε/3 := (le_trans (hNx hn.left).le p6)
  calc
    _ < _ := p5
    _ = |(y n - y0) * (x n - x0)| + 2*ε/3 := by ring
    _ ≤ _ := addLeAddMpr p7 (2*ε/3)
    _ = _ := by ring

/-
#check tsum
#check Metric.ball

lemma tsumOverNatImpliesConvergent {f:ℕ->ℝ} {s:ℝ} (h:Summable f): 
tsum f = s -> sequenceN.convergesTo (fun n=>((List.range n).map f).sum) s := by
  intro h1; simp [tsum,h] at h1; have p1:=choose_spec h
  rw [HasSum] at p1; rw [h1,Filter.Tendsto] at p1
  refine' convergesInRealIff.mpr _
  intro ε hε
  have p2:Metric.ball s ε ∈ nhds s := by 
    rw [mem_nhds_iff]
    exact ⟨Metric.ball s ε,subset_rfl,metricBallIsOpen ,by simp [hε]⟩ 
  replace p1:=Filter.mem_map.mp (Filter.le_def.mp p1 _ p2)
  simp at p1
  refine' Exists.elim p1 _
  intro A hA
  by_cases c1:0< A.card 
  case neg =>
    push_neg at c1; simp at c1
    refine' ⟨0,_ ⟩ 
    intro n _
    have p3: List.sum (List.map f (List.range n)) = Finset.sum (Finset.range n) fun b => f b

-/


/-

         
--1. R中收敛序列有界
--2. lim 乘法 加法
--3. LIM 得到 EReal中收敛 (从而在R中收敛)
--4. limsup liminf 的性质 
--5. 单调有界必收敛
6. R中闭区间是紧集
7. 一致收敛必连续
8. 闭区间上一致连续
    (闭球套 推广到测度空间的紧集上)
--9. LIM的唯一性
--10. 夹逼定理

(9) 各种收敛的例子用到再补充



    
    -/

















