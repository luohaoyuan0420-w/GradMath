import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.EReal
import GradMath.Basic.Basic

noncomputable section

namespace SUP_INF

open REAL

def SUP' :(Set Real) ->EReal :=  by
  intro s
  by_cases h1:s.Nonempty 
  · by_cases h2:BddAbove s
    · exact
      (Classical.choose (Real.exists_isLUB s h1 h2)).toEReal
    · exact ⊤ 
  · exact ⊥ 

def INF' :(Set Real) ->EReal := by
  intro s
  let s':Set Real := by 
    intro x;exact s (-x)
  exact (- (SUP' s'))

notation:100 "+∞" => (⊤:EReal)
notation:100 "-∞" => (⊥:EReal)

def boundedAbove' (s:Set Real):Prop:= ∃(M:Real), ∀{x}, (x∈s)->x≤M

def boundedBelow' (s:Set Real):Prop:= ∃(M:Real), ∀{x}, (x∈s)->M≤x

lemma sup'CloseEnough.aux {s:Set Real} (H1:s.Nonempty) (H2:BddAbove s):
∀{ε:Real},(0<ε)-> (∃x,(x∈s)∧(SUP' s< x+ε)) := by
  intro ε h1
  set M:=SUP' s with HH
  rw [SUP'] at HH
  simp [H1,H2] at HH
  let HH':=HH
  replace HH := congrArg EReal.toReal HH
  simp [IsLUB,IsLeast] at HH
  let p1:=Classical.choose_spec (Real.exists_isLUB s H1 H2)
  simp [IsLUB,IsLeast] at p1; rw [HH.symm] at p1
  by_contra hc ;simp [not_exists.mp] at hc
  let p2:=p1.right; simp [lowerBounds] at p2
  have p3:(SUP' s).toReal -ε ∈  upperBounds s := by 
    simp [upperBounds]
    intro a h2
    have p4:a+ε≤(SUP' s).toReal := by
      rw [HH];
      refine' EReal.coe_le_coe_iff.mp _
      have p5_1:SUP' s ≠ ⊤ := by rw [HH'];simp
      have p5_2:SUP' s ≠ ⊥ := by rw [HH'];simp
      rw [HH.symm];rw [EReal.coe_toReal p5_1 p5_2]
      exact  (hc a h2)
    calc 
      a = a+ε-ε := by simp 
      _ ≤ _ :=(add_le_add_iff_right (-ε)).mpr p4
  replace p3:=p2 p3;simp at p3
  have p4:=calc 
    0 < _ :=h1
    _ ≤ 0 := p3
  simp at p4

lemma boundedAbove'toBddAbove {s:Set Real}: (boundedAbove' s) -> (BddAbove s) :=by
  intro h
  simp [BddAbove,upperBounds]
  refine' Set.nonempty_def.mpr _
  simp [ boundedAbove'] at h
  refine' Exists.elim h _
  intro M h3
  have p1:M ∈ {x | ∀ ⦃a : ℝ⦄, a ∈ s → a ≤ x} := by 
    simp ; intro a; exact h3
  exact ⟨M,p1 ⟩ 

lemma sup'CloseEnough {s:Set Real} (h1:s.Nonempty) (h2:boundedAbove' s):
∀{ε:Real},(0<ε)-> (∃x,(x∈s)∧(SUP' s< x+ε)) := 
  sup'CloseEnough.aux h1 ( boundedAbove'toBddAbove h2)
  
lemma inf'CloseEnough {s:Set Real} (H1:s.Nonempty) (H2:boundedBelow' s):
∀{ε:Real},(0<ε)-> (∃x,(x∈s)∧(x-ε<INF' s)) := by 
  intro ε h1
  simp [INF'] ;simp [Set.Nonempty] at H1
  let s':Set Real := by 
    intro x;exact s (-x)
  simp [boundedBelow'] at H2
  have p1:boundedAbove' s' := by
    simp [boundedAbove']
    refine' Exists.elim H2 _
    intro M h2
    have p2:∀ {x' : ℝ}, (x' ∈ s') → x' ≤ -M  := by
      intro x' h3
      simp [Set.mem_def] at h3
      let p3:= leFlip (h2 h3); simp at p3
      exact p3
    exact ⟨-M,p2⟩ 
  have p2:s'.Nonempty := by 
    refine' Exists.elim H1 _
    intro x h2
    have p3: (-x)∈s' := by 
      simp [Set.mem_def] ;exact h2
    exact ⟨-x,p3⟩ 
  let p3 :=(sup'CloseEnough p2 p1) h1
  refine' Exists.elim p3 _
  intro x  h2
  refine' ⟨-x, _⟩ 
  have p4:(-x)∈s := by
    let p5:=h2.left
    simp [Set.mem_def] at p5;exact p5
  refine' ⟨p4,_⟩ 
  by_cases hc:BddAbove s'
  · set M:= SUP' s' with HH      
    replace h2:=h2.right
    rw [HH];rw [HH] at h2; rw [SUP'] at HH
    simp [hc,p2] at HH;rw [HH] at h2
    rw [HH,←EReal.coe_sub,←EReal.coe_neg];
    refine' EReal.coe_lt_coe_iff.mpr _
    rw [←EReal.coe_add] at h2
    replace h2:= ltFlip
      (EReal.coe_lt_coe_iff.mp h2)
    calc 
      -x - ε = -(x+ε) := by abel
      _ < _ := h2
  · exact absurd p1 hc 

lemma sup'Empty {s:Set Real} :(h: s=∅)-> SUP' s = -∞ := by
  intro h 
  let p1:=Set.not_nonempty_iff_eq_empty.mpr h
  simp [SUP',p1]

lemma inf'Empty {s:Set Real} :(h: s=∅)-> INF' s = +∞ := by
  intro h 
  let s':Set Real := by 
    intro x;exact s (-x) 
  have p1:s'=∅:= by
    refine' Set.eq_empty_iff_forall_not_mem.mpr _
    intro x 
    by_contra hc
    simp [Set.mem_def] at hc
    let p2:=(Set.eq_empty_iff_forall_not_mem.mp h) (-x)
    simp [Set.mem_def] at p2
    exact p2 hc
  replace p1:=Set.not_nonempty_iff_eq_empty.mpr p1
  simp [INF',SUP',p1]

lemma sup'boundedAbove'IsReal {s:Set Real} (H1:s.Nonempty) (H2:BddAbove s):
∃ M:Real, SUP' s = M := by
  set M := SUP' s with HH
  rw [SUP'] at HH
  simp [H1,H2] at HH
  exact ⟨(Classical.choose (_ : ∃ x, IsLUB s x)),HH⟩   

lemma notBoundedAbove'Iff {s:Set Real}: (¬(boundedAbove' s))↔(SUP' s = +∞)  := by
  have mp : (¬(boundedAbove' s)) ->(SUP' s = +∞)  := by
    intro h1
    have p1:¬ (BddAbove s) := by
      simp [BddAbove,upperBounds,Set.not_nonempty_iff_eq_empty,Set.eq_empty_iff_forall_not_mem]
      simp [boundedAbove'] at h1
      exact h1
    have h:s.Nonempty := by
      by_contra hc
      simp [boundedAbove'] at h1
      refine' Exists.elim (h1 0) _
      intro x h2
      have p1:s.Nonempty :=by
        simp [Set.Nonempty]
        exact ⟨_,h2.left⟩ 
      exact hc p1
    simp [SUP',p1,h]
  have mpr :(SUP' s = +∞) -> (¬(boundedAbove' s)) := by
    intro h1
    by_contra hc
    have h:s.Nonempty := by
      by_contra hc2
      simp [SUP',hc2] at h1
    let p1:=sup'boundedAbove'IsReal h hc
    refine' Exists.elim p1 _
    intro M h2
    rw [h1] at h2; simp at h2
  exact ⟨mp,mpr⟩

lemma inf'boundedBelow'IsReal {s:Set Real} (H1:s.Nonempty) (H2:boundedBelow' s):
∃ M:Real, INF' s = M := by
  let s':Set Real := by 
    intro x;exact s (-x) 
  simp [INF']
  have p1:s'.Nonempty := by
    rw [Set.Nonempty]
    simp [Set.Nonempty] at H1
    refine' Exists.elim H1 _
    intro x' h1
    have p2: (-x')∈s' := by 
      simp [Set.mem_def];exact h1
    exact ⟨-x',p2⟩  
  have p2: boundedAbove' s' := by
    simp [boundedAbove'] 
    simp [boundedBelow'] at H2
    refine' Exists.elim H2 _
    intro M h1
    have p3: ∀ {x : ℝ}, x∈s' → x ≤ -M := by
      intro x h2
      simp [Set.mem_def] at h2
      let p4:=leFlip (h1 h2)
      simp at p4
      exact p4
    exact ⟨_ ,p3⟩ 
  let p3:=  sup'boundedAbove'IsReal p1 p2
  refine' Exists.elim  p3 _
  intro M h2
  have p4: - (SUP' s') = ↑(-M) :=by
    simp;exact h2
  exact ⟨-M,p4⟩ 

lemma notBoundedBelow'Iff {s:Set Real}: (¬(boundedBelow' s))↔(INF' s = -∞)  := by
  set s':Set Real := by 
    intro x;exact s (-x) 
  simp [INF']
  have p1: boundedBelow' s = boundedAbove' s' := by 
    simp [boundedBelow',boundedAbove']
    have mp:(∃M,∀{x:ℝ},x∈s→M≤x)->∃M,∀{x:ℝ}, (x∈s')→x≤M := by
      intro h1
      refine' Exists.elim h1 _
      intro M h2
      have p2:∀ {x : ℝ}, x ∈ s' → x ≤ -M := by
        intro x h3
        simp [Set.mem_def] at h3
        let p3:=leFlip (h2 h3)
        simp at p3; exact p3
      exact ⟨_,p2⟩ 
    have mpr: (∃M,∀{x:ℝ}, (x∈s')→x≤M ) -> (∃M,∀{x:ℝ},x∈s→M≤x) := by
      intro h1
      refine' Exists.elim h1 _
      intro M h2
      have p2:∀ {x:ℝ}, x ∈ s → -M ≤ x  := by
        intro x h3
        have p3:(-x)∈s' := by simp [Set.mem_def];exact h3
        let p4:= leFlip (h2 p3)
        simp at p4; exact p4
      exact ⟨_,p2⟩ 
    exact ⟨mp,mpr⟩ 
  rw [p1]      
  exact notBoundedAbove'Iff 

end SUP_INF

namespace Set

def toEReal :(Set Real)->(Set EReal) := by
  intro s
  exact (
    fun (x:EReal) =>
      if (x≠+∞)∧(x≠-∞) 
        then  x.toReal ∈ s
        else False)

def toReal :(Set EReal)->(Set Real) := by
  intro s
  exact (fun x=>↑x∈s )

end Set

namespace SUP_INF

open REAL SET LIST

def SUP :(Set EReal)->(EReal) :=  by 
  intro s
  if (+∞ ∈ s) 
    then (exact +∞)
    else (
      exact  SUP' s.toReal
    )

def INF: (Set EReal)->(EReal) :=  by
  intro s
  if (-∞ ∈ s) 
    then (exact -∞)
    else (
      exact INF' s.toReal
    ) 

def boundedAbove (s:Set EReal):Prop:= ∃(M:Real), ∀{x}, (x∈s)->x≤M

def boundedBelow (s:Set EReal):Prop:= ∃(M:Real), ∀{x}, (x∈s)->M≤x

lemma setToRealNonemptyMp {s:Set EReal} :(s.toReal.Nonempty)->s.Nonempty :=by
  intro h1
  simp [Set.Nonempty,Set.toReal,Set.mem_def] at h1
  refine' Exists.elim h1 _
  intro x h2
  exact ⟨↑x,h2⟩ 

def toMemReal {x:EReal} {s:Set Real} :(h: x∈s.toEReal)->(x.toReal∈s) := by
  intro h
  simp [Set.toEReal,Set.mem_def] at h
  set p0:=(¬x = ⊤ ∧ ¬x = ⊥) with HH
  simp_rw [←HH ] at h
  by_cases c1:p0
  · simp [c1] at h
    exact h
  · simp [c1] at h

def toMemEReal {x:Real} {s:Set Real} :(h:x∈s)->(↑x∈s.toEReal) := by
  intro h
  simp [Set.toEReal,Set.mem_def]
  exact h

def toMemEReal' {x:Real}{s:Set EReal} :(h: x∈s.toReal)->(↑x∈s) := by
  intro h
  simp [Set.toReal,Set.mem_def] at h
  exact h

def toMemReal' {x:Real} {s:Set EReal} :(h:↑x∈s)->(↑x∈s.toReal) := by
  intro h
  simp [Set.toEReal,Set.mem_def]
  exact h

lemma supCloseEnough' {s:Set EReal} (h1:s.toReal.Nonempty) (h2:boundedAbove s):
∃M:Real, SUP s=M ∧ ( ∀{ε:Real},(0<ε)-> (∃x,(x∈s)∧(M< x+ε))) :=  by
  have p1: +∞ ∉ s := by
    by_contra hc
    simp [boundedAbove] at h2
    refine' Exists.elim h2 _
    intro M h3
    replace h3:=h3 hc;simp at h3
  set N:=SUP s  with HH
  rw [SUP] at HH; simp [p1] at HH
  have p2: boundedAbove' s.toReal:= by
    rw [boundedAbove']
    rw [boundedAbove] at h2
    refine' Exists.elim h2 _
    intro M h3 
    have p3:∀ {x : ℝ}, x ∈ Set.toReal s → x ≤ M :=by
      intro x h4
      let p4:=h3 (h4)
      simp at p4 ;exact p4
    exact ⟨_ ,p3⟩ 
  refine' Exists.elim (sup'boundedAbove'IsReal h1 p2) _
  intro M h3
  replace HH:= h3 ▸ HH
  have p3:∀ {ε:ℝ},0<ε→∃x,x∈s ∧ M<x+ε:= by
    intro ε h4
    let p4:= (sup'CloseEnough h1 p2)  h4
    rw [h3] at p4 ;
    refine' Exists.elim p4 _
    intro x h5
    exact ⟨x,h5⟩ 
  exact ⟨_,HH,p3⟩ 

lemma infCloseEnough' {s:Set EReal} (h1:s.toReal.Nonempty) (h2:boundedBelow s):
∃M:Real, INF s=M ∧ ( ∀{ε:Real},(0<ε)-> (∃x,(x∈s)∧(x-ε<M))) :=  by
  let s':Set EReal := by 
    intro x;exact s (-x)
  have p1: boundedAbove s' := by
    rw [boundedAbove]; rw [boundedBelow] at h2
    refine' Exists.elim h2 _
    intro M h3
    have p2: ∀ {x : EReal}, x ∈ s' → x ≤ ↑(-M) := by
      intro x h4
      simp [Set.mem_def] at h4
      replace h3:=  (h3 h4)
      match x with 
      | -∞ => simp
      | +∞ => 
        simp at h3
      | (x:Real) =>
        rw [← EReal.coe_neg,EReal.coe_le_coe_iff] at h3;
        replace h3:=leFlip h3; simp at h3
        exact EReal.coe_le_coe_iff.mpr  h3
    exact ⟨_,p2⟩ 
  have p2: s'.toReal.Nonempty := by
    simp [Set.Nonempty];simp [Set.Nonempty] at h1
    refine' Exists.elim h1 _
    intro x h3
    replace h3:=toMemEReal h3
    simp [Set.toEReal,Set.toReal,Set.mem_def] at h3
    have p3: (-(x.toEReal)) ∈ s'  := by 
      simp [Set.mem_def]; exact h3
    exact ⟨_,p3⟩ 
  refine' Exists.elim  (supCloseEnough' p2 p1) _
  intro M h3
  have p3: INF s = ↑(-M) := by
    simp [INF]
    have p4: +∞ ∉ s' := by
      by_contra hc
      let p5:=h3.left
      simp [SUP,hc] at p5
    have p5: -∞ ∉s := by
      simp [Set.mem_def] at p4
      simp [Set.mem_def] 
      exact p4
    simp [p5,INF']; 
    let p6:=h3.left
    simp [SUP,p4] at p6
    let s'':Set Real := by 
      intro x;exact s.toReal (-x)
    have p7: s''=s'.toReal := by
      simp [Set.ext_iff]
      intro x
      have mp: x∈s'' -> x∈s'.toReal := by
        intro h4
        simp [Set.mem_def,Set.toReal] at h4
        simp [Set.mem_def,Set.toReal];exact h4
      have mpr: x∈s'.toReal -> x∈s'' := by
        intro h4
        simp [Set.mem_def,Set.toReal] at h4
        simp [Set.mem_def,Set.toReal];exact h4
      exact ⟨mp,mpr⟩ 
    rw [p7.symm] at p6;exact p6
  have p4:∀{ε:ℝ}, 0<ε→∃x,x∈s∧x-↑ε<↑(-M) := by
    intro ε h4
    refine' Exists.elim (h3.right h4) _
    intro x h5
    set xx:=x with HH
    match xx with 
    | -∞ => 
      replace h5:=h5.right
      simp at h5
    | +∞ =>
      let p5:=h3.left
      simp [SUP,h5.left] at p5
    | (x':ℝ) =>
      have p5:-x - ↑ε < ↑(-M) := by
        rw [HH.symm,← EReal.coe_neg,←EReal.coe_sub]
        refine' EReal.coe_lt_coe_iff.mpr _
        replace h5:=h5.right
        rw [←EReal.coe_add] at h5
        replace h5:=ltFlip (EReal.coe_lt_coe_iff.mp h5)
        calc 
          _ = -(x' + ε) := by abel
          _ < _ := h5
      have p6: (-x) ∈ s := by
        let p7:=HH ▸ h5.left
        simp [Set.mem_def] at p7
        exact p7
      exact ⟨_,p6,p5⟩ 
  exact ⟨_,p3,p4⟩ 

lemma notBoundedAboveIff {s:Set EReal} : 
(¬(boundedAbove s))↔(SUP s = +∞)  := by
  have mp:(¬(boundedAbove s))->(SUP s = +∞) := by
    intro h1
    simp [SUP] 
    by_cases hc: +∞ ∈ s
    · simp [hc]
    · simp [hc]
      simp [boundedAbove] at h1
      have p1: ¬(boundedAbove' s.toReal) := by
        simp [boundedAbove']
        intro M
        refine' Exists.elim (h1 M) _
        intro x h2  
        let p2:=h2.right
        set xx:=x with HH
        match xx with 
        | -∞ =>
          simp at p2
        | +∞ =>
          refine' absurd h2.left hc
        | (x':Real) =>
          have p3: x'∈ s.toReal := by
            simp [Set.toReal,Set.mem_def]
            exact h2.left
          let p4:=EReal.coe_lt_coe_iff.mp h2.right
          exact ⟨_,p3,p4⟩ 
      by_cases hc2: s.toReal.Nonempty
      · exact (notBoundedAbove'Iff).mp p1
      · simp [boundedAbove'] at p1
        refine' Exists.elim (p1 0) _
        intro x h2
        have p2:s.toReal.Nonempty := by
          simp [Set.Nonempty]
          exact ⟨_,h2.left⟩ 
        exact absurd p2 hc2
  have mpr: (SUP s = +∞) -> ¬(boundedAbove s) := by
    intro h1
    simp [SUP] at h1 ;simp [boundedAbove]
    by_cases hc : +∞ ∈ s
    · intro x
      have p1: x<  +∞  := by
        simp
      exact ⟨_,hc,p1⟩ 
    · simp [hc] at h1
      intro M
      by_cases hc2 : s.toReal.Nonempty 
      · let p1:= (notBoundedAbove'Iff).mpr h1
        simp [boundedAbove'] at p1
        refine' Exists.elim (p1 M) _
        intro x h2
        exact ⟨_,toMemEReal' h2.left,
          EReal.coe_lt_coe_iff.mpr h2.right⟩ 
      · simp [SUP',hc2] at h1
  exact ⟨mp,mpr⟩ 

lemma notBoundedBelowIff {s:Set EReal} : 
(¬(boundedBelow s))↔(INF s = -∞)  := by
  have mp:(¬(boundedBelow s))->(INF s = -∞) := by
    intro h1
    simp [INF] 
    by_cases hc: -∞ ∈ s
    · simp [hc]
    · simp [hc]
      simp [boundedBelow] at h1
      have p1: ¬(boundedBelow' s.toReal) := by
        simp [boundedBelow']
        intro M
        refine' Exists.elim (h1 M) _
        intro x h2  
        let p2:=h2.right
        set xx:=x with HH
        match xx with 
        | +∞ =>
          simp at p2
        | -∞ =>
          refine' absurd h2.left hc
        | (x':Real) =>
          have p3: x'∈ s.toReal := by
            simp [Set.toReal,Set.mem_def]
            exact h2.left
          let p4:=EReal.coe_lt_coe_iff.mp h2.right
          exact ⟨_,p3,p4⟩ 
      by_cases hc2: s.toReal.Nonempty
      · exact (notBoundedBelow'Iff).mp p1
      · simp [boundedBelow'] at p1
        refine' Exists.elim (p1 0) _
        intro x h2
        have p2:s.toReal.Nonempty := by
          simp [Set.Nonempty]
          exact ⟨_,h2.left⟩ 
        exact absurd p2 hc2
  have mpr: (INF s = -∞) -> ¬(boundedBelow s) := by
    intro h1
    simp [INF] at h1 ;simp [boundedBelow]
    by_cases hc : -∞ ∈ s
    · intro x
      have p1: -∞<x  := by
        simp
      exact ⟨_,hc,p1⟩ 
    · simp [hc] at h1
      intro M
      by_cases hc2 : s.toReal.Nonempty 
      · let p1:= (notBoundedBelow'Iff).mpr h1
        simp [boundedBelow'] at p1
        refine' Exists.elim (p1 M) _
        intro x h2
        exact ⟨_,toMemEReal' h2.left,
          EReal.coe_lt_coe_iff.mpr h2.right⟩ 
      · let s':Set EReal := by 
          intro x;exact s (-x)
        have p1:¬ s'.toReal.Nonempty := by
          by_contra hc3
          simp [Set.Nonempty,Set.mem_def] at hc3
          refine' Exists.elim hc3 _
          intro x h2
          have p2:s.toReal.Nonempty := by
            simp [Set.Nonempty]
            exact ⟨_,h2⟩ 
          exact absurd p2 hc2
        simp [INF',SUP'] at h1
        let s'':Set Real := by 
          intro x;exact s.toReal (-x)
        have p2: s''=s'.toReal := by
          simp [Set.ext_iff]
          intro x
          have mp: x∈s'' -> x∈s'.toReal := by
            intro h4
            simp [Set.mem_def,Set.toReal] at h4
            simp [Set.mem_def,Set.toReal];exact h4
          have mpr: x∈s'.toReal -> x∈s'' := by
            intro h4
            simp [Set.mem_def,Set.toReal] at h4
            simp [Set.mem_def,Set.toReal];exact h4
          exact ⟨mp,mpr⟩ 
        simp_rw [← p2] at p1
        simp [p1] at h1
  exact ⟨mp,mpr⟩ 

lemma supEmpty {s:Set EReal} (h:s=∅) : SUP s = -∞  := by
  have p1:¬(+∞ ∈ s) := by
    by_contra hc
    simp [setEqEmptyIff] at h
    exact (h (+∞) hc)
  have p2:¬s.toReal.Nonempty := by
    simp [Set.Nonempty]
    intro x
    by_contra hc
    replace hc:= toMemEReal' hc
    simp [setEqEmptyIff] at h
    exact h (↑x) hc
  simp [SUP,p1,SUP',p2]

lemma infEmpty {s:Set EReal} (h:s=∅) : INF s = +∞  := by
  have p1:¬(-∞ ∈ s) := by
    by_contra hc
    simp [setEqEmptyIff] at h
    exact (h (-∞) hc)
  have p2:¬s.toReal.Nonempty := by
    simp [Set.Nonempty]
    intro x
    by_contra hc
    replace hc:= toMemEReal' hc
    simp [setEqEmptyIff] at h
    exact h (↑x) hc
  let s':Set EReal := by 
    intro x;exact s (-x)
  have p3:¬ s'.toReal.Nonempty := by
    by_contra hc3
    simp [Set.Nonempty,Set.mem_def] at hc3
    refine' Exists.elim hc3 _
    intro x h2
    have p4:s.toReal.Nonempty := by
      simp [Set.Nonempty]
      exact ⟨_,h2⟩ 
    exact absurd p4 p2
  let s'':Set Real := by 
      intro x;exact s.toReal (-x)
  have p4: s''=s'.toReal := by
    simp [Set.ext_iff]
    intro x
    have mp: x∈s'' -> x∈s'.toReal := by
      intro h4
      simp [Set.mem_def,Set.toReal] at h4
      simp [Set.mem_def,Set.toReal];exact h4
    have mpr: x∈s'.toReal -> x∈s'' := by
      intro h4
      simp [Set.mem_def,Set.toReal] at h4
      simp [Set.mem_def,Set.toReal];exact h4
    exact ⟨mp,mpr⟩ 
  simp_rw [p4.symm] at p3
  simp [INF,p1,INF',SUP',p3]

lemma supIsUpperBound {s:Set EReal} {x:EReal} :(x∈s) -> (x≤SUP s) := by
  intro h
  by_cases c1: +∞ ∈ s 
  · simp [SUP,c1]
  · simp [SUP,c1]
    by_cases c2: s.toReal.Nonempty
    · simp [SUP',c2]
      by_cases c3: BddAbove s.toReal
      · simp [c3]
        let p1:=Real.exists_isLUB  s.toReal c2 c3
        let p2:=Classical.choose_spec  p1
        set M:=Classical.choose p1 with HH
        simp [IsLUB,IsLeast] at p2
        simp_rw [← HH] at p2
        replace p2:=p2.left
        rw [upperBounds,Set.mem_def,Set.setOf_set ] at p2
        match x with 
        | +∞ =>
          exact absurd h c1
        | -∞ =>
          simp 
        | (x':Real) =>
          exact EReal.coe_le_coe_iff.mpr (p2 (toMemReal' h))
      · simp [c3]
    · simp [SUP',c2]
      match x with
      | +∞ => 
        exact absurd h c1
      | -∞ =>
        rfl
      | (x':Real) =>
        replace h:=toMemReal' h
        replace c2:=(setEqEmptyIff.mp (setNotNonemptyIff.mp c2)) x'
        exact absurd h c2
          
lemma infIsLowerBound {s:Set EReal} {x:EReal} :(x∈s) -> (INF s≤x) := by
  intro h
  let s':Set EReal := by 
    intro x;exact s (-x)
  by_cases c1: -∞ ∈ s 
  · simp [INF,c1]
  · simp [INF,c1]
    simp [INF']
    have p1: -x ∈ s':= by
      simp [Set.mem_def]
      exact h
    replace p1:=supIsUpperBound p1
    have p2: ¬(+∞ ∈ s') := by
      simp [Set.mem_def];exact c1
    simp [SUP,p2] at p1
    simp [EReal.neg_le];exact p1

def setERealFlip :(Set EReal) -> Set EReal := by
  intro s 
  let s':Set EReal := by 
    intro x;exact s (-x)
  exact s'

@[simp]
lemma memFlipIff {s:Set EReal}{x:EReal}: x∈setERealFlip s ↔  -x ∈ s := by
  have mp: x∈setERealFlip s ->  -x ∈ s  := by
    intro h1; simp [setERealFlip,Set.mem_def] at h1;
    exact h1
  have mpr: -x ∈ s -> x∈ setERealFlip s := by
    intro h1; simp [setERealFlip,Set.mem_def]
    exact h1
  exact ⟨mp,mpr⟩ 

lemma infIsNegSupFlip {s:Set EReal} : INF s = - SUP (setERealFlip s) := by
  simp [INF]
  by_cases c1: -∞∈ s
  · have p1 :+∞∈ setERealFlip s  := by
      simp [setERealFlip,Set.mem_def];
      exact c1
    simp [c1,SUP,p1]
  · have p1 :¬( +∞∈ setERealFlip s)  := by
      by_contra hc
      simp [setERealFlip,Set.mem_def] at hc
      exact c1 hc
    simp [c1,SUP,p1,INF']
    rw [setERealFlip];rfl

lemma supIsNegInfFlip {s:Set EReal} : SUP s = - INF (setERealFlip s) := by
  let p1:=@infIsNegSupFlip (setERealFlip s)
  rw [p1]
  have p2: setERealFlip ((setERealFlip s)) = s := by
    simp [SET.setEqIff]
  rw [p2];simp
      
lemma supIsLeastUpperBound {s:Set EReal}{x:EReal}:(∀{y:EReal},y∈s->y≤x) -> (SUP s≤x) := by
  intro h1
  match x with 
  | +∞ =>
    simp
  | (x':ℝ) =>
    have p1:boundedAbove s := by
      simp [boundedAbove];
      exact ⟨_,h1⟩ 
    have p2: ¬ (+∞ ∈ s) := by
      by_contra hc1
      let p3:= h1 hc1
      simp at p3
    by_cases c1:s.toReal.Nonempty
    case pos =>
      refine' Exists.elim (supCloseEnough' c1 p1) _
      intro M h2
      by_contra hc
      rw [h2.left] at hc
      push_neg at hc; simp at hc
      have p3: 0 < (M-x') *(1/2) := by
        simp;exact hc
      refine' Exists.elim (h2.right p3) _
      intro y h3
      match y with 
      | +∞ =>
        simp [boundedAbove] at p1
        refine' Exists.elim p1 _
        intro N h4
        replace h4:=h4 h3.left
        simp at h4
      | -∞ =>
        let p4:=h3.right
        simp at p4
      | (y':ℝ ) =>
        replace h1:=h1 h3.left
        simp at h1
        let p4:=h3.right; rw [← EReal.coe_add] at p4
        replace p4:= (
          EReal.coe_lt_coe_iff.mp p4 )
        have p5': 0 < M - x'- (M - x') * 2⁻¹ := by
          calc 
            0 < (M - x') *(1/2) := p3
            _ = M - x'- (M - x') * 2⁻¹  := by ring
        replace p5':= addLtAddMpr p5'  ((M - x') * 2⁻¹)
        simp at p5'
        have p5: y'+(M-x')*(1/2) < y'+(M-x') := by
          rw [add_comm y',add_comm y']
          refine' (addLtAddMpr _ y' )
          simp;exact p5'
        have p6:= calc 
          M < _ := p4
          y'+(M-x')*(1/2) < y'+(M-x') := p5
          _ ≤ x' + (M-x') := addLeAddMpr h1 _
          _ = M := by simp
        simp at p6
    case neg =>
      simp [SUP,p2,SUP',c1]
  | -∞ =>
    have p1: ¬ (+∞ ∈ s) := by 
      by_contra hc
      let p1:=h1 hc
      simp at p1
    have p2: ¬s.toReal.Nonempty := by
      by_contra hc
      simp [Set.Nonempty] at hc
      refine' Exists.elim hc _
      intro y h2
      replace h2:=toMemEReal h2
      replace h1:= h1 h2
      simp at h1
    simp [SUP,p1,SUP',p2]

lemma infIsGreatestLowerBound {s:Set EReal}{x:EReal}:(∀{y:EReal},y∈s->x≤y) -> (x≤INF s) := by
  intro h1
  have p1: ∀ {y : EReal}, y ∈ setERealFlip s → y≤-x := by
    intro y h2
    simp [Set.mem_def,setERealFlip] at h2
    exact EReal.le_neg_of_le_neg (h1 h2)
  rw [infIsNegSupFlip]
  refine' EReal.le_neg_of_le_neg _
  exact supIsLeastUpperBound p1

lemma supCloseEnough {s:Set EReal} {r:Real}(h:SUP s = ↑r):
∀{ε:Real},(0<ε)-> ∃x:ℝ,(↑x∈s)∧(SUP s< ↑(x+ε)) :=  by
  intro ε  hε 
  have p1:s.toReal.Nonempty := by
    simp [Set.Nonempty,Set.toReal,Set.mem_def]
    by_contra hc; push_neg at hc
    have p2:SUP s = +∞ ∨ SUP s = -∞  := by
      by_cases c:+∞ ∈ s
      · exact Or.inl (le_antisymm  (by simp) (supIsUpperBound c))
      · by_cases c2:-∞ ∈ s 
        · have p3:s={-∞} := by
            refine' setEqIff.mpr _
            intro z
            have mp:z ∈ s -> z ∈ ({⊥}:Set EReal) := by
              intro h1; simp
              match z with
              | +∞ =>
                exact absurd  h1 c
              | -∞ =>
                rfl
              | (z':Real) =>
                exact absurd h1 (hc z')
            have mpr: z ∈ ({⊥}:Set EReal) -> z∈s := by
              intro h1; simp at h1
              rw [h1]; exact c2
            exact ⟨mp,mpr⟩ 
          have p4:∀{y:EReal},y∈s->y≤-∞  := by
            intro y hy; rw [p3] at hy; simp at hy; rw [hy]
          replace p4:=supIsLeastUpperBound p4
          simp at p4; exact Or.inr p4
        · have p4:s=∅ := by
            by_contra hc2; 
            refine' Exists.elim (setNonemptyIff.mpr hc2) _
            intro a ha
            match a with 
            | +∞ =>
              exact c ha
            | -∞ =>
              exact c2 ha
            | (a':Real) =>
              exact (hc a') ha
          exact Or.inr (supEmpty p4)
    rw [h] at p2; simp at p2
  have p2: boundedAbove s := by
    refine' ⟨r,_ ⟩ 
    intro x hx
    let p3:=supIsUpperBound hx;rw [h] at p3
    exact p3
  refine' Exists.elim (supCloseEnough' p1 p2) _
  intro M hM
  refine' Exists.elim (hM.right hε) _
  intro a ha
  match a with
  | +∞ =>
    let p3:=supIsUpperBound ha.left
    rw [hM.left] at p3; simp at p3
  | -∞ =>
    simp at ha
  | (a':Real) =>
    refine' ⟨ _,ha.left,_⟩ 
    rw [hM.left];exact ha.right

lemma infCloseEnough {s:Set EReal} {r:Real}(h:INF s = ↑r):
∀{ε:Real},(0<ε)-> ∃x:ℝ,(↑x∈s)∧(↑(x-ε)<INF s) :=  by
  intro ε  hε 
  have p1:s.toReal.Nonempty := by
    simp [Set.Nonempty,Set.toReal,Set.mem_def]
    by_contra hc; push_neg at hc
    have p2:INF s = -∞ ∨ INF s = +∞  := by
      by_cases c:-∞ ∈ s
      · exact Or.inl (le_antisymm (infIsLowerBound c) (by simp))
      · by_cases c2:+∞ ∈ s 
        · have p3:s={+∞} := by
            refine' setEqIff.mpr _
            intro z
            have mp:z ∈ s -> z ∈ ({⊤}:Set EReal) := by
              intro h1; simp
              match z with
              | -∞ =>
                exact absurd  h1 c
              | +∞ =>
                rfl
              | (z':Real) =>
                exact absurd h1 (hc z')
            have mpr: z ∈ ({⊤}:Set EReal) -> z∈s := by
              intro h1; simp at h1
              rw [h1]; exact c2
            exact ⟨mp,mpr⟩ 
          have p4:∀{y:EReal},y∈s->+∞≤ y  := by
            intro y hy; rw [p3] at hy; simp at hy; rw [hy]
          replace p4:=infIsGreatestLowerBound p4
          simp at p4; exact Or.inr p4
        · have p4:s=∅ := by
            by_contra hc2; 
            refine' Exists.elim (setNonemptyIff.mpr hc2) _
            intro a ha
            match a with 
            | -∞ =>
              exact c ha
            | +∞ =>
              exact c2 ha
            | (a':Real) =>
              exact (hc a') ha
          exact Or.inr (infEmpty p4)
    rw [h] at p2; simp at p2
  have p2: boundedBelow s := by
    refine' ⟨r,_ ⟩ 
    intro x hx
    let p3:=infIsLowerBound hx;rw [h] at p3
    exact p3
  refine' Exists.elim (infCloseEnough' p1 p2) _
  intro M hM
  refine' Exists.elim (hM.right hε) _
  intro a ha
  match a with
  | -∞ =>
    let p3:=infIsLowerBound ha.left
    rw [hM.left] at p3; simp at p3
  | +∞ =>
    simp at ha
  | (a':Real) =>
    refine' ⟨ _,ha.left,_⟩ 
    rw [hM.left];exact ha.right

lemma INFleSUP {s:Set EReal}(h:s.Nonempty): INF s ≤ SUP s := by
  by_contra hc; push_neg at hc
  refine' Exists.elim h _
  intro a ha
  have p1:= calc
    _ < _ :=hc
    _ ≤ a :=infIsLowerBound ha
    _ ≤ _ :=supIsUpperBound ha
  simp at p1

lemma supEqPosInftyIff {s:Set EReal} : SUP s = +∞ ↔ ∀(r:ℝ),∃x, x∈s∧ r< x := by
  have mp: SUP s = +∞ -> (∀(r:ℝ),∃x, x∈s∧ r< x):= by
    intro h1 r ; by_contra hc; push_neg at hc
    replace hc:∀ {x : EReal}, x ∈ s → x ≤ ↑r:= hc _
    replace hc:=supIsLeastUpperBound hc; rw [h1] at hc
    simp at hc
  have mpr: (∀(r:ℝ),∃x, x∈s∧ r< x) -> SUP s = +∞ := by
    intro h1
    set M:= SUP s with HH
    match M with
    | -∞ =>
      refine' Exists.elim (h1 0) _
      intro a ha
      have p2:= calc
        _ = _ :=HH.symm
        _ < ↑0 := by simp
        _ < _ :=ha.right
        _ ≤ _ := supIsUpperBound ha.left
      simp at p2
    | +∞ => rfl
    | (M':ℝ) =>
      refine' Exists.elim (h1 M') _
      intro a ha
      have p1:= calc
        SUP s = _ :=HH.symm
        _ < a :=ha.right
        _ ≤ _ :=supIsUpperBound ha.left
      simp at p1
  exact ⟨mp,mpr ⟩ 
    
lemma infEqNegInftyIff {s:Set EReal} : INF s = -∞ ↔ ∀(r:ℝ),∃x, x∈s∧ x<r := by
  have mp: INF s = -∞ -> (∀(r:ℝ),∃x, x∈s∧ x<r):= by
    intro h1 r ; by_contra hc; push_neg at hc
    replace hc:∀ {x : EReal}, x ∈ s → ↑r≤x:= hc _
    replace hc:=infIsGreatestLowerBound hc; rw [h1] at hc
    simp at hc
  have mpr: (∀(r:ℝ),∃x, x∈s∧ x<r) -> INF s = -∞ := by
    intro h1
    set M:= INF s with HH
    match M with
    | +∞ =>
      refine' Exists.elim (h1 0) _
      intro a ha
      have p2:= calc
        _ ≤ _ := infIsLowerBound ha.left
        _ < _ :=ha.right
        ↑0 < +∞  := by simp
        _ = _ :=HH
      simp at p2
    | -∞ => rfl
    | (M':ℝ) =>
      refine' Exists.elim (h1 M') _
      intro a ha
      have p1:= calc
        _ ≤ _ :=infIsLowerBound ha.left
        _ < _ :=ha.right
        _ = _ :=HH
      simp at p1
  exact ⟨mp,mpr ⟩ 
    
universe u_1

instance : Lattice EReal := by infer_instance

lemma erealNegSup {x y :EReal} : -(x⊔y) = (-x)⊓(-y) := by
  by_cases c1:x≤y
  · have p1:y≤x⊔y :=  by simp
    have p2: x⊔y ≤ y := sup_le c1 ((by simp):y≤ y)
    replace p1:=le_antisymm p1 p2
    rw [p1.symm]; simp; exact c1
  · push_neg at c1
    replace c1:=c1.le
    have p1:x≤x⊔y :=  by simp
    have p2: x⊔y ≤ x := sup_le  ((by simp):x≤ x) c1
    replace p1:=le_antisymm p1 p2
    rw [p1.symm]; simp; exact c1

lemma erealNegInf {x y :EReal} : -(x⊓y) = (-x)⊔(-y) := by
  by_cases c1: x≤y
  · have p1:x⊓y≤x :=  by simp
    have p2: x≤x⊓y  := le_inf  ((by simp):x≤ x) c1
    replace p1:=le_antisymm p1 p2
    rw [p1.symm]; simp;
  · push_neg at c1
    replace c1:=c1.le
    have p1:x⊓y≤y :=  by simp
    have p2: y≤x⊓y  := le_inf c1 ((by simp):y≤ y)
    replace p1:=le_antisymm p1 p2
    rw [p1]; simp; exact c1

open Set
lemma supOfUnion {A B:Set EReal}: SUP (A∪B) = (SUP A)⊔(SUP B) := by
  have p1:SUP (A∪B) ≤  (SUP A) ⊔ (SUP B) := by
    by_cases c1: A.Nonempty
    case neg =>
      by_cases c2:B.Nonempty 
      case neg =>
        have p1: ¬ (A∪B).Nonempty := by
          by_contra hc
          simp [Nonempty] at hc
          cases' hc with h1 h2
          · exact c1 h1
          · exact c2 h2 
        have p2:  A=∅   := by   
          refine' setEqEmptyIff.mpr _
          intro x
          by_contra hc
          exact (setEqEmptyIff.mp (setNotNonemptyIff.mp p1)) _ 
            ((mem_union x A B).mpr (Or.inl hc))
        replace p1:=supEmpty (setNotNonemptyIff.mp p1)
        replace p2:=supEmpty p2
        rw [p1,p2];simp
      case pos =>
        have p1:(A∪B) ⊆ B := by
          refine' setSubsetIff.mpr _
          intro x h1
          simp at h1
          cases' h1 with h1_1 h1_2
          · simp [setNotNonemptyIff,setEqEmptyIff] at c1
            exact absurd h1_1 (c1 x)
          · exact h1_2
        have p2:B ⊆ (A∪B) := by simp
        let p3:=setEqMpr p1 p2
        rw [p3]
        let p4:=supEmpty (setNotNonemptyIff.mp c1)
        rw [p4];simp
    case pos =>
      by_cases c2:B.Nonempty 
      case neg =>
        let p1:=supEmpty (setNotNonemptyIff.mp c2)
        have p2:(A∪B) ⊆ A := by
          refine' setSubsetIff.mpr _
          intro x h1
          simp at h1
          cases' h1 with h1_1 h1_2
          · exact h1_1
          · simp [setNotNonemptyIff,setEqEmptyIff] at c2
            exact absurd h1_2 (c2 x)
        have p3: A ⊆ (A∪B) := by simp
        replace p3:=setEqMpr p2 p3
        rw [p3,p1];simp
      case pos =>
        by_cases c3:boundedAbove A
        case pos =>
          by_cases c4:boundedAbove B
          case pos =>
            by_cases c5:A.toReal.Nonempty 
            case pos => 
              simp [Set.Nonempty] at c5
              have p3: ∀{y},(y∈A∪B)->y≤ SUP A ⊔ SUP B :=by
                intro y h1
                simp at h1
                cases' h1 with h1_1 h1_2
                · let p4:=supIsUpperBound h1_1
                  calc 
                    y ≤ SUP A := p4
                    _ ≤ _ := by simp
                · let p4:=supIsUpperBound h1_2
                  calc 
                    y ≤ SUP B := p4
                    _ ≤ _ := by simp
              exact supIsLeastUpperBound p3
            case neg =>
              by_cases c6: +∞∈A
              case pos =>
                have p2:+∞∈ A∪B := by simp;exact Or.inl c6
                rw [SUP,SUP]; simp only [c6,p2]; simp
              case neg =>
                have p2: ∀{y},(y∈A∪B)->y≤ SUP A ⊔ SUP B :=by
                  intro y h1
                  cases' h1 with h1_1 h1_2
                  · have p2: y=-∞ := by
                      match y with
                      | -∞ =>  rfl
                      | +∞ => 
                        exact absurd h1_1 c6
                      | (x':ℝ) =>
                        replace c5:= (setEqEmptyIff.mp
                          (setNotNonemptyIff.mp c5)) ↑x'
                        exact absurd h1_1 c5
                    rw [p2];simp
                  · let p2:=supIsUpperBound h1_2
                    calc 
                      y ≤ SUP B := p2
                      _ ≤ SUP A ⊔ SUP B := by simp
                exact supIsLeastUpperBound p2
          case neg =>
            let p1:=notBoundedAboveIff.mp c4
            rw [p1];simp
        case neg =>
          rw [notBoundedAboveIff.mp c3]; simp
  have p2:SUP A ⊔ SUP B ≤ SUP (A ∪ B) := by
    let p3:=@supIsUpperBound (A ∪ B)
    have p4: ∀{y},(y∈A)->y≤ SUP (A ∪ B) := by
      intro y h1
      have p4:y ∈ A∪B := by 
        simp ; exact Or.inl h1
      exact p3 p4
    have p5: ∀{y},(y∈B)->y≤ SUP (A ∪ B) := by
      intro y h1
      have p6:y ∈ A∪B := by
        simp ; exact Or.inr h1
      exact p3 p6
    replace p4:=supIsLeastUpperBound p4
    replace p5:=supIsLeastUpperBound p5
    exact sup_le p4 p5
  exact le_antisymm p1 p2

lemma infOfUnion {A B:Set EReal}: INF (A∪B) = (INF A)⊓(INF B) := by 
  rw [infIsNegSupFlip,infIsNegSupFlip,infIsNegSupFlip]
  rw [←erealNegSup];simp
  have p1: setERealFlip (A∪B) = (setERealFlip A)∪(setERealFlip B) := by
    refine' setEqIff.mpr _
    intro x
    have mp:x∈setERealFlip (A∪B) -> x∈(setERealFlip A ∪ setERealFlip B) := by
      intro h1;
      simp [setERealFlip,mem_def] at h1
      simp  [setERealFlip,mem_def]
      exact h1
    have mpr:  x∈(setERealFlip A ∪ setERealFlip B) -> x∈setERealFlip (A∪B) := by
      intro h1 
      simp [setERealFlip,mem_def] at h1
      simp [setERealFlip,mem_def]
      exact h1
    exact ⟨mp,mpr⟩ 
  rw [p1] ; exact supOfUnion
            
lemma supMono {A B:Set EReal}: (A⊆B) -> (SUP A ≤ SUP B) := by
  intro h
  have p1:A∪B=B := by simp [h]
  calc 
    SUP A ≤ (SUP A) ⊔ (SUP B) := by simp
    _ = SUP (A∪B) := supOfUnion.symm
    _ = SUP B := by rw [p1]

lemma infMono {A B:Set EReal}: (A⊆B) -> (INF B ≤ INF A) := by
  intro h
  have p1:A∪B=B := by simp [h]
  calc 
    INF B ≤ INF (A∪B) := by rw [p1]
    _ = _  := infOfUnion
    _ ≤  INF A := by simp

def Max: List ℝ -> EReal := 
fun l => l.foldr (fun x y=>(x.toEReal)⊔y) (-∞ )

def Min: List ℝ -> EReal :=
fun l => l.foldr (fun x y=>(x.toEReal)⊓y) (+∞ )

lemma maxIsGreatest {l:List ℝ} {x:ℝ} : (x∈l) -> ↑x ≤ Max l := by
  intro h
  match l with
  | [] =>
    simp at h
  | a::l' =>
    simp at h
    cases' h with h_1 h_2
    · simp [Max]
      have p1:x.toEReal ≤ a.toEReal := by 
        rw [h_1]
      replace p1:=EReal.coe_le_coe_iff.mp p1 
      exact Or.inl p1
    · simp [Max]
      let p1:=maxIsGreatest h_2
      simp [Max] at p1
      exact Or.inr p1

lemma maxIsReachable {l:List ℝ}: (l≠[])-> ∃(n:Nat)(p:n<l.length),(↑l[n]=Max l) := by
  intro h
  match l with
  | [] =>
    simp at h
  | a::l' =>
    set x:= Max (a::l') with HH
    rw [Max] at HH
    simp at HH
    by_cases hc1: a≤Max l'
    · simp [Max] at hc1
      simp [hc1] at HH
      by_cases hc2: l'≠[]
      · refine' Exists.elim (maxIsReachable hc2)  _
        intro n h1
        refine' Exists.elim h1 _
        intro h1 h2
        have p1: n.succ <(a::l').length := by 
          simp 
          exact  Nat.succ_lt_succ h1
        have p2:↑ (a::l')[n.succ] = Max l' := by 
          simp ;exact h2
        rw [Max,HH.symm] at p2
        exact ⟨_,p1,p2⟩ 
      · push_neg at hc2
        simp [hc2] at hc1
    · push_neg at hc1
      simp [Max] at hc1
      simp [hc1.le] at HH
      have p1: ↑(a::l')[0]= x := by 
        simp; exact HH.symm
      have p2: 0 < (a::l').length := by simp
      exact ⟨_,p2,p1⟩ 
      
lemma maxEqSup {l:List ℝ}: SUP l.toFinset.toSet.toEReal = Max l := by
  have p1: SUP l.toFinset.toSet.toEReal ≤ Max l := by
    have p2:∀{x:EReal}, (x∈l.toFinset.toSet.toEReal) -> x ≤ Max l := by
      intro x h1
      let p3:=toMemReal h1
      simp at p3
      match x with 
      | +∞ =>
        simp [Set.toEReal,Set.mem_def] at h1
      | -∞ =>
        simp [Set.toEReal,Set.mem_def] at h1
      | (x':Real) =>
        replace h1:=toMemReal h1
        simp at h1
        exact maxIsGreatest h1
    exact supIsLeastUpperBound p2
  have p2:Max l ≤ SUP l.toFinset.toSet.toEReal := by
    by_cases hc : l ≠ []
    · refine' Exists.elim (maxIsReachable hc) _
      intro n h1
      refine' Exists.elim h1 _
      intro h2 h3
      have p2: ↑(List.get l ⟨n,h2⟩  ) ∈ l.toFinset.toSet.toEReal := by
        simp [Set.toEReal,Set.mem_def,setOf]
        exact listGetIsMem h2
      have p3: ↑(List.get l { val := n, isLt := h2 }) = Max l  := h3
      rw [p3] at p2
      exact supIsUpperBound p2
    · push_neg at hc
      simp [hc,Max,SUP]
  exact le_antisymm p1 p2
          
lemma minIsLeast {l:List ℝ} {x:ℝ} : (x∈l) -> Min l ≤ ↑ x := by
  intro h
  match l with
  | [] =>
    simp at h
  | a::l' =>
    simp at h
    cases' h with h_1 h_2
    · simp [Min]
      have p1: a.toEReal≤ x.toEReal := by 
        rw [h_1]
      replace p1:=EReal.coe_le_coe_iff.mp p1 
      exact Or.inl p1
    · simp [Min]
      let p1:=minIsLeast h_2
      simp [Min] at p1
      exact Or.inr p1

lemma minIsReachable {l:List ℝ}: (l≠[])-> ∃(n:Nat)(p:n<l.length),(↑l[n]=Min l) := by
  intro h
  match l with
  | [] =>
    simp at h
  | a::l' =>
    set x:= Min (a::l') with HH
    rw [Min] at HH
    simp at HH
    by_cases hc1: Min l' ≤ a
    · simp [Min] at hc1
      simp [hc1] at HH
      by_cases hc2: l'≠[]
      · refine' Exists.elim (minIsReachable hc2)  _
        intro n h1
        refine' Exists.elim h1 _
        intro h1 h2
        have p1: n.succ <(a::l').length := by 
          simp 
          exact  Nat.succ_lt_succ h1
        have p2:↑ (a::l')[n.succ] = Min l' := by 
          simp ;exact h2
        rw [Min,HH.symm] at p2
        exact ⟨_,p1,p2⟩ 
      · push_neg at hc2
        simp [hc2] at hc1
    · push_neg at hc1
      simp [Min] at hc1
      simp [hc1.le] at HH
      have p1: ↑(a::l')[0]= x := by 
        simp; exact HH.symm
      have p2: 0 < (a::l').length := by simp
      exact ⟨_,p2,p1⟩ 
      
lemma minEqInf {l:List ℝ}: INF l.toFinset.toSet.toEReal = Min l := by
  have p1:Min l ≤  INF l.toFinset.toSet.toEReal  := by
    have p2:∀{x:EReal}, (x∈l.toFinset.toSet.toEReal) -> Min l ≤ x := by
      intro x h1
      let p3:=toMemReal h1
      simp at p3
      match x with 
      | +∞ =>
        simp [Set.toEReal,Set.mem_def] at h1
      | -∞ =>
        simp [Set.toEReal,Set.mem_def] at h1
      | (x':Real) =>
        replace h1:=toMemReal h1
        simp at h1
        exact minIsLeast h1
    exact infIsGreatestLowerBound p2
  have p2: INF l.toFinset.toSet.toEReal ≤ Min l:= by
    by_cases hc : l ≠ []
    · refine' Exists.elim (minIsReachable hc) _
      intro n h1
      refine' Exists.elim h1 _
      intro h2 h3
      have p2: ↑(List.get l ⟨n,h2⟩  ) ∈ l.toFinset.toSet.toEReal := by
        simp [Set.toEReal,Set.mem_def,setOf]
        exact listGetIsMem h2
      have p3: ↑(List.get l { val := n, isLt := h2 }) = Min l  := h3
      rw [p3] at p2
      exact infIsLowerBound p2
    · push_neg at hc
      simp [hc,INF,Min]
  exact le_antisymm p2 p1

end SUP_INF




























