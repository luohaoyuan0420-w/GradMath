import GradMath.Topology.PointSet.CompactnessConnectedness
import Mathlib.Topology.MetricSpace.Basic
import GradMath.Basic.Rat
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Order.Filter.AtTopBot
import GradMath.Basic.Sort

noncomputable section

namespace METRIC

universe u_1 u_2
variable {α:Type u_1} {β:Type u_2}

open COUNTABLE Set PointSetTopology SET Classical LIST

def metricSpaceMK {ρ:α->α ->ℝ} (ρNonNeg:∀{x y:α},0≤ ρ x y)
(ρZeroIff:∀{x y:α}, ρ x y = 0 ↔ x = y) 
(triangel: ∀{x y z:α}, (ρ x y) ≤ (ρ x z) + (ρ y z) ):MetricSpace α :={
  dist:=ρ  
  dist_self:= fun _=> ρZeroIff.mpr rfl
  dist_comm:= by
    intro x y
    let p1:= @triangel x y x; simp [(@ρZeroIff x x ).mpr  ] at p1
    let p2:= @triangel y x y; simp [(@ρZeroIff y y ).mpr  ] at p2
    exact le_antisymm p1 p2
  dist_triangle := by
    intro x z y
    let p1:= @triangel y z y; simp [(@ρZeroIff y y ).mpr  ] at p1
    let p2:= @triangel z y z; simp [(@ρZeroIff z z ).mpr  ] at p2
    let p3:= le_antisymm p1 p2
    let p4:=p3 ▸ @triangel x y z
    exact p4
  edist_dist := by 
    intro x y; simp [ENNReal.ofReal,Real.toNNReal,ρNonNeg]
  eq_of_dist_eq_zero := by
    intro x y h ; exact ρZeroIff.mp h}

def pseudoMetricSpaceMK {ρ:α->α ->ℝ} (ρNonNeg:∀{x y:α},0≤ ρ x y)
(ρZeroMpr:∀{x y:α},x=y-> ρ x y = 0 ) 
(triangel: ∀{x y z:α}, (ρ x y) ≤ (ρ x z) + (ρ y z) ):PseudoMetricSpace α :={
  dist:=ρ  
  dist_self:= fun _=> ρZeroMpr rfl
  dist_comm:= by
    intro x y
    let p1:= @triangel x y x; simp [(@ρZeroMpr x x )  ] at p1
    let p2:= @triangel y x y; simp [(@ρZeroMpr y y )  ] at p2
    exact le_antisymm p1 p2
  dist_triangle := by
    intro x z y
    let p1:= @triangel y z y; simp [(@ρZeroMpr y y )  ] at p1
    let p2:= @triangel z y z; simp [(@ρZeroMpr z z )  ] at p2
    let p3:= le_antisymm p1 p2
    let p4:=p3 ▸ @triangel x y z
    exact p4
  edist_dist := by 
    intro x y; simp [ENNReal.ofReal,Real.toNNReal,ρNonNeg]}

lemma openIff [PseudoMetricSpace α] {s:Set α} :
IsOpen s ↔ ∀ {x : α}, x ∈ s → (∃ (ε : ℝ) (_: ε > 0), Metric.ball x ε ⊆ s) :=by
  simp [Metric.isOpen_iff]

lemma metricBallIsOpen  [PseudoMetricSpace α] {r:Real} {x:α} :IsOpen (Metric.ball x r) := by 
  by_cases c:r>0
  case neg =>
    have p1: Metric.ball x r = ∅ := by 
      simp; push_neg at c; exact c
    rw [p1]; exact emptyIsOpen
  case pos =>
    refine' openIff.mpr _
    intro y hy; simp at hy
    refine' ⟨r- dist y x , by simp [hy],_  ⟩ 
    intro z hz; simp ; simp at hz
    replace hz :=REAL.addLtAddMpr hz (dist y x)
    simp at hz
    calc
      dist z x ≤  dist z y + dist y x := dist_triangle _ _ _
      _ < r := hz
  
instance [PseudoMetricSpace α]:fstCountable α := by 
  have p1:(∀ (x : α), ∃ nbB:neighbBasis x, Set.atMostCountable nbB.neighbs) := by
    intro x
    have p2:{q:ℚ | q>0}.Nonempty := ⟨1,by simp ⟩ 
    replace p2:=subsetOfCountable p2 (by simp) QIsCountable
    refine' Exists.elim p2 _
    intro f _
    let g:Subtype ({q:ℚ | q>0}) -> neighb x :=
      fun q =>⟨Metric.ball x q.val,by simp;exact q.property,metricBallIsOpen ⟩ 
    replace p2:Im(g,univ).atMostCountable := imageOfCountable _ (subtypeIsCountable p2)
    let nbB:neighbBasis x := {
      neighbs := Im(g,univ)
      exists_contained := by
        intro nb
        refine' Exists.elim (openIff.mp nb.property.right nb.property.left) _
        intro r hr
        refine' Exists.elim hr _
        intro p3 hr
        refine' Exists.elim (RAT.ratBetweenAnyReals p3) _
        intro q hq ; simp at hq;
        have p4:g ⟨q,hq.left⟩ ∈ Im(g,univ) := by
          simp only [mem_image]
          refine' ⟨⟨q,hq.left⟩,by simp,rfl ⟩ 
        refine' ⟨_,p4,subset_trans _ hr ⟩ 
        intro z hz; simp; simp at hz
        exact   lt_trans  hz hq.right}
    exact ⟨nbB,p2 ⟩ 
  exact ⟨p1⟩ 

@[simp]
def IsCauchy [PseudoMetricSpace α] (x:sequenceN α) :Prop :=
∀{ε:Real}, 0<ε ->∃N:Nat,∀{n m:Nat}, (N≤n ∧ N≤m) -> dist (x n) (x m) < ε 

lemma completeDef [Nonempty α] [pm:PseudoMetricSpace α] :
CompleteSpace α ↔ ∀{x:sequenceN α}, IsCauchy x->∃ x0:α , x.convergesTo x0 := by
  have mp:CompleteSpace α  -> 
  (∀{x:sequenceN α}, IsCauchy x->∃ x0:α , x.convergesTo x0) := by
    intro h1 x h2
    let fil:=Filter.generate (Im(fun n=>Im(x,{m:ℕ| n≤m }) ,(univ:Set ℕ)))
    let p1:fil.NeBot := by
      refine' Filter.generate_neBot_iff.mpr _
      intro S hS1 hS2
      have p2:∀{t:Set α}, t∈S -> ∃n:Nat, t= Im(x,{m:ℕ| n≤m }) := by
        intro  t ht
        replace ht:=setSubsetIff.mp hS1 _ ht
        simp at ht; refine' Exists.elim ht _
        intro n hn; exact ⟨_,hn.symm ⟩ 
      let setNat:=Im( fun x=>choose (p2 x.property) ,(univ:Set (Subtype S)))
      have p3:setNat.Finite :=by
        exact Finite.image _ (@finite_univ _ (Finite.to_subtype hS2))
      by_cases c: S.Nonempty
      case neg =>
        replace c:=setNotNonemptyIff.mp c
        rw [c]; simp
      case pos =>
        have p4: 0<p3.toFinset.toList.length  := by
          by_contra hc; simp at hc
          refine' Exists.elim c _
          intro a ha; exact (hc a) ha
        have p5:0<(p3.toFinset.toList.mergeSort (.≥.)).length := by 
          rw [List.length_mergeSort]; exact p4
        set M:=(p3.toFinset.toList.mergeSort (.≥.))[0]
        have p6:∀{m:Nat}, m∈p3.toFinset -> m≤ M := by
          intro m hm
          by_cases c : m=M
          · exact c.le
          · have p7:m∈(p3.toFinset.toList.mergeSort (.≥.)) := by
              refine' (@memSortIffMemOrig _ (.≥.)  _ _ m).mpr _
              rw [Finset.mem_toList]; exact hm
            exact (sortFirstIsMax  (.≥.) p3.toFinset.toList p4) p7 c
        refine' ⟨x M,_ ⟩ 
        rw [mem_sInter]; intro t ht
        have p7: choose (p2 ht)∈ setNat := by
          rw [mem_image]; refine' ⟨⟨_,ht ⟩,by simp  ⟩ 
        rw [choose_spec (p2 ht),mem_image]
        exact ⟨M,p6 ((Finite.mem_toFinset p3).mpr p7),rfl ⟩ 
    have p2:Cauchy fil := by  
      refine'  Metric.cauchy_iff.mpr ⟨p1,_ ⟩ 
      intro ε hε; 
      refine' Exists.elim (h2 hε) _
      intro N hN
      have p3:Im(x,{m:ℕ|N≤m })∈ fil := by
        refine' Filter.mem_generate_iff.mpr ⟨{Im(x,{m:ℕ| N≤m })} ,by simp,by simp,_⟩ 
        intro z hz; simp at hz;simp; exact hz
      refine' ⟨_,p3,_ ⟩ 
      intro x1 hx1 x2 hx2
      refine' Exists.elim hx1 _
      intro n1 hn1; simp at hn1
      refine' Exists.elim hx2 _
      intro n2 hn2; simp at hn2
      rw [hn1.right.symm,hn2.right.symm]
      exact hN ⟨hn1.left,hn2.left ⟩ 
    refine' Exists.elim (h1.complete p2) _
    intro x0 hx0
    refine' ⟨x0,_ ⟩ ;simp 
    intro u
    have p3:u.set ∈ nhds x0 := by
      refine' mem_nhds_iff.mpr _
      refine' ⟨u.set,subset_rfl,u.property.right,u.property.left ⟩ 
    refine' Exists.elim (Filter.mem_generate_iff.mp (Filter.le_def.mp hx0 _ p3)) _
    intro S hS 
    refine' Exists.elim hS _
    intro hS1 hS2
    have p2':∀{t:Set α}, t∈S -> ∃n:Nat, t= Im(x,{m:ℕ| n≤m }) := by
      intro  t ht
      replace ht:=setSubsetIff.mp hS1 _ ht
      simp at ht; refine' Exists.elim ht _
      intro n hn; exact ⟨_,hn.symm ⟩ 
    let setNat:=Im( fun x=>choose (p2' x.property) ,(univ:Set (Subtype S)))
    have p3':setNat.Finite :=by
      exact Finite.image _ (@finite_univ _ (Finite.to_subtype hS2.left))
    by_cases c: S.Nonempty
    case neg =>
      replace c:=setNotNonemptyIff.mp c
      rw [c] at hS2; simp at hS2
      replace hS2:=subset_antisymm hS2 (by simp)
      refine' ⟨0,by rw [hS2.symm];simp ⟩ 
    case pos =>
      have p4': 0<p3'.toFinset.toList.length  := by
          by_contra hc; simp at hc
          refine' Exists.elim c _
          intro a ha; exact (hc a) ha
      have p5':0<(p3'.toFinset.toList.mergeSort (.≥.)).length := by 
          rw [List.length_mergeSort]; exact p4'
      set M:=(p3'.toFinset.toList.mergeSort (.≥.))[0]
      have p6':∀{m:Nat}, m∈p3'.toFinset -> m≤ M := by
        intro m hm
        by_cases c : m=M
        · exact c.le
        · have p7':m∈(p3'.toFinset.toList.mergeSort (.≥.)) := by
            refine' (@memSortIffMemOrig _ (.≥.)  _ _ m).mpr _
            rw [Finset.mem_toList]; exact hm
          exact (sortFirstIsMax  (.≥.) p3'.toFinset.toList p4') p7' c
      refine' ⟨M,_ ⟩ 
      intro n hn; refine' setSubsetIff.mp hS2.right _ _
      simp; intro t ht
      have p7': choose (p2' ht)∈ setNat := by
          rw [mem_image]; refine' ⟨⟨_,ht ⟩,by simp  ⟩ 
      rw [choose_spec (p2' ht),mem_image]
      exact ⟨n,le_trans (p6' ((Finite.mem_toFinset p3').mpr p7')) hn,rfl ⟩ 
  have mpr: (∀{x:sequenceN α}, IsCauchy x->∃ x0:α , x.convergesTo x0)->CompleteSpace α := by
    intro h; refine' Metric.complete_of_cauchySeq_tendsto _
    intro x hx; replace hx:=Metric.cauchySeq_iff.mp hx
    have p1: IsCauchy x := by
      simp; intro ε hε 
      refine' Exists.elim (hx _ hε) _
      intro N hN
      refine' ⟨N,_ ⟩ 
      intro n m hn hm
      exact hN _ hn _ hm
    refine' Exists.elim (h p1) _
    intro x0 hx0; simp only [sequenceN.convergesTo] at hx0
    refine' ⟨ x0,_⟩ ;simp [Filter.Tendsto]
    refine' Filter.le_def.mpr _
    intro u hu; 
    refine' Filter.mem_map.mpr _
    refine' Exists.elim (mem_nhds_iff.mp hu) _
    intro u' hu'
    refine' Exists.elim (hx0 ⟨_,hu'.right.right,hu'.right.left ⟩ ) _
    intro N hN
    have p2:{k:ℕ | N≤ k} ⊆ PreIm(x,u) := by
      intro k hk; 
      refine' setSubsetIff.mp hu'.left _ _
      exact hN hk
    exact Filter.sets_of_superset _ (Filter.mem_atTop _)  p2
  exact ⟨mp,mpr⟩ 

lemma totallyBoundedDef [PseudoMetricSpace α] {s:Set α} :TotallyBounded s ↔ 
∀ {ε : ℝ}, ε > 0 → (∃ (t : Set α), t.Finite ∧ s ⊆ ⋃ (y : α) (_ : y ∈ t), Metric.ball y ε) := by
  simp [Metric.totallyBounded_iff]

lemma seqCompactDef  [PseudoMetricSpace α] {s:Set α} :
IsSeqCompact s ↔ ∀{x:sequenceN α},(∀(n:ℕ),x n ∈ s) -> 
∃(x0:α)(_:x0∈s)(φ:ℕ->ℕ), StrictMono φ ∧ sequenceN.convergesTo (x∘φ) x0 := by
  have mp: IsSeqCompact s -> (∀{x:sequenceN α},(∀(n:ℕ),x n ∈ s) -> 
  ∃(x0:α)(_:x0∈s)(φ:ℕ->ℕ), StrictMono φ ∧ sequenceN.convergesTo (x∘φ) x0 ):= by
    intro h1 x hx; simp only [IsSeqCompact] at h1
    refine' Exists.elim (h1 hx) _
    intro x0 hx0
    refine' Exists.elim hx0.right _
    intro φ hφ
    refine' ⟨_,hx0.left,_,hφ.left,_  ⟩ 
    exact CoeMathlib.tendstoConvergesTo.mp hφ.right
  have mpr: (∀{x:sequenceN α},(∀(n:ℕ),x n ∈ s) -> 
  ∃(x0:α)(_:x0∈s)(φ:ℕ->ℕ), StrictMono φ ∧ sequenceN.convergesTo (x∘φ) x0 )->IsSeqCompact s := by
    intro h; simp [IsSeqCompact]
    intro x hx
    refine' Exists.elim (h hx) _
    intro x0 hx0
    refine' Exists.elim hx0 _
    intro p1 hx0
    refine' Exists.elim hx0 _
    intro φ hφ
    refine' ⟨_,p1,_,hφ.left,_  ⟩ 
    exact CoeMathlib.tendstoConvergesTo.mpr hφ.right
  exact ⟨mp,mpr⟩ 
  
lemma closedCompleteTotallyBoundedIsCompact [PseudoMetricSpace α] [CompleteSpace α] {s:Set α}
(h1:TotallyBounded s) (h2:IsClosed s) :IsCompact s := 
isCompact_of_totallyBounded_isClosed h1 h2

lemma compactImpliesSeqCompact [PseudoMetricSpace α] {s:Set α} (h:IsCompact s):
IsSeqCompact s :=IsCompact.isSeqCompact h

lemma seqCompactImpliesTotallyBounded [PseudoMetricSpace α] {s:Set α} (h:IsSeqCompact s):
TotallyBounded s :=IsSeqCompact.totallyBounded h

end METRIC














