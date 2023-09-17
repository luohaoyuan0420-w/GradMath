import Mathlib.Topology.SubsetProperties
import GradMath.Topology.PointSet.Constructions
import Mathlib.Topology.Connected
import Mathlib.Topology.PathConnected

noncomputable section

namespace  PointSetTopology

open FUNCTION SET Set LIST FINSET Classical  NAT COUNTABLE

universe u_1 u_2
variable {α: Type u_1} {β :Type u_2}

lemma compactDef [TopologicalSpace α] {s:Set α} :
IsCompact s ↔ ∀ cover:openCover s, ∃cover':openCover s,
cover'.sets.Finite ∧ cover'.sets ⊆ cover.sets := by 
  have mp: IsCompact s -> ∀ cover:openCover s, ∃cover':openCover s, 
  cover'.sets.Finite ∧ cover'.sets ⊆ cover.sets := by
    intro h1 cover
    let p1:=cover.is_covered; rw [setSUnionEqUnion] at p1
    refine' Exists.elim (isCompact_iff_finite_subcover.mp h1 (Subtype.val:(Subtype cover.sets)->Set α)
      (fun x=>cover.sets_forall_open x.property) p1) _
    intro fs hfs
    let cover':openCover s := {
      sets:=Im(Subtype.val,fs.toSet)
      sets_forall_open := by
        intro s' hs'; 
        refine' Exists.elim hs' _
        intro s hs; rw [hs.right.symm]
        exact cover.sets_forall_open s.property
      is_covered:= by
        have p2:(⋃ (i:Subtype cover.sets) (_:i∈fs), i.val) = ⋃₀ Im(Subtype.val,fs.toSet) := by
          refine' setEqIff.mpr _
          intro x
          have mp:x∈ (⋃ (i:Subtype cover.sets) (_:i∈fs), i.val) 
          ->x∈ ⋃₀ Im(Subtype.val,fs.toSet) := by
            intro h1; simp ; simp at h1; exact h1
          have mpr: x∈ ⋃₀ Im(Subtype.val,fs.toSet) ->
          x∈ (⋃ (i:Subtype cover.sets) (_:i∈fs), i.val) := by
            intro h1; simp; simp at h1; exact h1
          exact ⟨mp,mpr⟩ 
        rw [p2.symm]; exact hfs }
    have p2:cover'.sets.Finite := by
      refine' Finite.image _ _
      simp
    have p3: cover'.sets ⊆ cover.sets := by
      refine' setSubsetIff.mpr _
      intro x hx; refine' Exists.elim hx _
      intro s hs; rw [hs.right.symm]; exact s.property
    exact ⟨_,p2,p3 ⟩ 
  have mpr:( ∀ cover:openCover s, ∃cover':openCover s, 
  cover'.sets.Finite ∧ cover'.sets ⊆ cover.sets ) -> IsCompact s := by
    intro h1
    have p1:∀{ι:Type u_1}(si:ι→ Set α),(∀(i:ι),IsOpen (si i)) → (s ⊆ ⋃ (i:ι), si i) 
    → (∃ (t : Finset ι), s ⊆ ⋃ (i : ι) (_ : i ∈ t), si i) := by
      intro ι si hsi1 hsi2
      let cover:openCover s :={
        sets:=Im(si,univ)
        sets_forall_open:= by
          intro s hs; refine' Exists.elim hs _
          intro i hi; rw [hi.right.symm]
          exact hsi1 i
        is_covered := by
          rw [← setUnionEqSUnion]
          exact hsi2   }
      refine' Exists.elim (h1 cover) _
      intro cover' hcover'
      have p1:∀{t:Set α},t∈cover'.sets->∃i:ι,si i = t := by
        intro t ht; refine' Exists.elim 
          ((mem_image _ _ _).mp (setSubsetIff.mp hcover'.right _ ht)) _
        intro i hi; exact ⟨_,hi.right⟩ 
      let fs:=Im(fun x=>choose (p1 x.property),(univ:Set (Subtype cover'.sets)))
      have p2:fs.Finite := by
        refine' (Finite.image _ ) _
        have p3:Finite (Subtype cover'.sets):= Finite.to_subtype hcover'.left
        exact finite_univ          
      refine' ⟨Finite.toFinset p2,setSubsetIff.mpr _ ⟩ 
      intro x hx; simp
      refine' Exists.elim (mem_sUnion.mp (setSubsetIff.mp (cover'.is_covered) _ hx)) _
      intro t ht; let p3:= choose_spec (p1 ht.left)
      refine' ⟨choose (p1 ht.left),⟨t,_⟩,p3.symm ▸ ht.right  ⟩ ;
      simp; exact ht.left
    exact isCompact_iff_finite_subcover.mpr p1
  exact ⟨mp,mpr⟩ 

lemma compactIffSubspaceCompact [TopologicalSpace α] {s:Set α}:
IsCompact s ↔ IsCompact (univ:(Set (Subtype s))) := isCompact_iff_isCompact_univ

lemma imageOfCompact [TopologicalSpace α][TopologicalSpace β] {f:α->β} {s:Set α} 
(h1:IsCompact s)(h2:Continuous f):IsCompact (Im(f,s)) :=IsCompact.image h1 h2

lemma closedSetInCompact [TopologicalSpace α] {s:Set α} (h1:IsCompact (univ:Set α))
(h2:IsClosed s): IsCompact s :=
  @IsClosed.isCompact _ _ ⟨h1⟩ _  h2

lemma closedCompactInterIsCompact [TopologicalSpace α] {s t:Set α} (h1:IsCompact s)
(h2:IsClosed t): IsCompact (s ∩ t) := by
  let p1:=IsCompact.inter_left h1 h2
  rw [Set.inter_comm]; exact p1
        
lemma compactIsClosedInHausdorff [TopologicalSpace α] [hs:HausdorffSpace α] {s:Set α}
(h:IsCompact s) : IsClosed s := by
  have p1: s = (sᶜ)ᶜ := setComplCompl.symm
  rw [p1];refine' openComplIsClosed (openMpr _)
  intro x hx
  have p2:∀{y},y∈s -> y≠x := by
    intro y hy; by_contra hc
    rw [hc] at hy; exact hx hy
  let f:Subtype s->Set α × Set α :=
    fun y'=>⟨(choose (hs.property (p2 y'.property ))).set,
      (choose (choose_spec (hs.property (p2 y'.property )))).set⟩ 
  have hf:∀(y':Subtype s), (f y').1 ∩ (f y').2 =∅  :=
    fun y' => (choose_spec (choose_spec (hs.property (p2 y'.property ))))
  let cover:openCover s := {
    sets :=Im(fun y'=>(f y').1,(univ:Set (Subtype s)))
    sets_forall_open:=by
      intro t ht; simp at ht
      refine' Exists.elim ht _
      intro y ht
      refine' Exists.elim ht _
      intro hy ht; rw [ht.symm]
      exact (choose (hs.property (p2 hy ))).property.right
    is_covered := by
      refine' setSubsetIff.mpr _
      intro y hy ; simp only [mem_sUnion]
      refine' ⟨(choose (hs.property (p2 hy ))).set,
        by simp only [mem_image];exact ⟨⟨ y,hy⟩ ,by simp,rfl ⟩,_ ⟩ 
      exact (choose (hs.property (p2 hy ))).property.left}
  refine' Exists.elim (compactDef.mp h cover) _
  intro subcover Hsubcover
  have p3:∀{t:Set α}, t∈subcover.sets -> ∃ y':Subtype s, t = (f y').1 :=by
    intro t ht; replace ht:=setSubsetIff.mp Hsubcover.right _ ht
    simp only [mem_image] at ht
    refine' Exists.elim ht _
    intro y' hy'
    exact ⟨_,hy'.right.symm ⟩ 
  let pairs_chosen:=Im(fun t'=>f (choose (p3 t'.property)), (univ:Set (Subtype subcover.sets)))
  have p4:⋃₀ subcover.sets ⊆ ⋃₀ Im(Prod.fst,pairs_chosen) := by
    refine' setSubsetIff.mpr _
    intro z hz; simp only [mem_sUnion] at hz
    refine' Exists.elim hz _
    intro t ht;
    have p5:f (choose (p3 ht.left)) ∈ pairs_chosen := by
      simp; exact ⟨t,ht.left,rfl,rfl ⟩ 
    have p6:(f (choose (p3 ht.left))).1 ∈ Im(Prod.fst,pairs_chosen) := by
      rw [mem_image];exact ⟨_,p5,rfl ⟩ 
    simp only [mem_sUnion]; refine' ⟨_,p6,_ ⟩ 
    let p7:=choose_spec ( p3 ht.left)
    exact p7 ▸ ht.right
  have p5:⋃₀ Im(Prod.fst,pairs_chosen) ∩ ⋂₀ Im(Prod.snd,pairs_chosen) = ∅ := by
    by_contra hc; replace hc:=setNonemptyIff.mpr hc
    refine' Exists.elim hc _
    intro y hy; replace hy:=(mem_inter_iff _ _ _).mp  hy
    rw [mem_sUnion] at hy
    refine' Exists.elim hy.left _
    intro t ht; replace hy:=hy.right
    rw [mem_image] at ht
    refine' Exists.elim ht.left _
    intro pair Hpair
    have p6:⋂₀ Im(Prod.snd,pairs_chosen) ⊆ pair.2 := by
      refine' setSubsetIff.mpr _
      intro z hz; 
      let p7:=(mem_image Prod.snd pairs_chosen pair.2).mpr ⟨_,Hpair.left,rfl ⟩ 
      simp only [mem_sInter] at hz; replace hz:=hz _ p7
      exact hz
    replace p6:=mem_inter (Hpair.right.symm ▸ht.right) (setSubsetIff.mp p6 _ hy)
    replace Hpair:=Hpair.left; rw [mem_image] at Hpair
    refine' Exists.elim Hpair _
    intro y' hy'
    let p7:=hf (choose (p3 y'.property))
    rw [hy'.right] at p7; rw [p7] at p6
    simp at p6
  have p6:Im(Prod.snd,pairs_chosen).Finite:= by 
    refine' Finite.image _ (Finite.image _ _ )
    exact @finite_univ _ (finite_coe_iff.mpr Hsubcover.left)
  have p7:∀{t:Set α}, t∈ (Im(Prod.snd,pairs_chosen)) -> x∈t ∧ IsOpen t := by
    intro t ht; rw [mem_image] at ht
    refine' Exists.elim ht _
    intro pair Hpair
    refine' Exists.elim Hpair.left _
    intro tt htt; rw [Hpair.right.symm,htt.right.symm]
    exact (choose (choose_spec (hs.property (p2 (choose (p3 tt.property)).property)))).property
  let ft:=p6.toFinset
  have p8:ft.toSet =  Im(Prod.snd,pairs_chosen) := by simp
  rw [p8.symm] at p7
  have p9:IsOpen (⋂₀ ft.toSet) :=finsetOpenInter (fun  h=> (p7 h).right)
  have p10:x∈(⋂₀ ↑ft) := by
    rw [mem_sInter]
    intro t ht; exact (p7 ht).left
  refine' ⟨⟨_,p10,p9⟩,_  ⟩ 
  calc 
    ⋂₀ ↑ft =  ⋂₀ Im(Prod.snd,pairs_chosen) := by rw [p8]
    _ ⊆ _ :=Disjoint.subset_compl_left (Set.disjoint_iff_inter_eq_empty.mpr p5)
    _ ⊆ _ :=setSubsetCompl.mpr p4
    _ ⊆ _ :=setSubsetCompl.mpr subcover.is_covered
  
lemma closedMapLemma [TopologicalSpace α] [TopologicalSpace β] [HausdorffSpace β] {f:α->β}
(h1:IsCompact (univ:Set α)) (h2:Continuous f) :IsClosedMap f := by
  simp only [IsClosedMap]
  intro u hu
  replace hu:=compactIffSubspaceCompact.mp (closedSetInCompact h1 hu)
  let p1:= imageOfCompact hu (continuousComp h2 subtypeValIsContinuous)
  have p2: Im((f ∘ Subtype.val),(univ:Set (Subtype u))) = Im(f,u) := by 
    refine' setEqIff.mpr _
    intro z 
    have mp: z ∈ Im((f ∘ Subtype.val),(univ:Set (Subtype u))) -> z ∈ Im(f,u) :=by
      intro H; simp only [mem_image] at H
      refine' Exists.elim H _
      intro z' hz'; simp; simp at hz'
      exact ⟨_,z'.property,hz'⟩ 
    have mpr:  z ∈ Im(f,u) -> z ∈ Im((f ∘ Subtype.val),(univ:Set (Subtype u))) := by
      intro H;simp; simp at H
      refine' Exists.elim H _
      intro z' hz'; exact ⟨_,hz' ⟩ 
    exact ⟨mp,mpr⟩ 
  rw [p2.symm]
  exact compactIsClosedInHausdorff p1

lemma compactUnion [TopologicalSpace α] {s t:Set α} (h1:IsCompact s) (h2:IsCompact t):
IsCompact (s∪t) := IsCompact.union h1 h2

lemma finsetCompactUnion [TopologicalSpace α] {S:Finset (Set α )}
(h:∀{s:Set α }, s∈S -> IsCompact s ) :IsCompact (⋃₀ S.toSet) := by
  let rec aux {l:List (Set α)} (haux:∀{si:Set α},si∈ l ->IsCompact si) :
  IsCompact (l.foldr (.∪.) ∅) := by
    match l with
    |[] =>  simp
    |ti::l' =>
      simp
      refine' compactUnion (@haux ti (by simp)) _
      have haux': ∀{si:Set α},si∈ l' ->IsCompact si := by
        intro si hsi
        have p2:si ∈ ti :: l' := by simp [hsi]
        exact haux p2
      exact aux haux'
  rw [← foldrUnionEqSUnion]
  have p1:∀{si:Set α},si∈ S.toList ->IsCompact si := by
    intro si hsi; simp at hsi
    exact h hsi
  exact aux p1

lemma connectedDef [TopologicalSpace α][Nonempty α] :
IsConnected (univ:Set α) ↔ ∀{u1 u2:Set α},
(IsOpen u1 ∧ IsOpen u2) ->u1 ∩ u2=∅ ∧ u1∪ u2=univ ->u1=∅ ∨ u2=∅  := by
  have mp: IsConnected (univ:Set α) -> 
  (∀{u1 u2:Set α},IsOpen u1 ∧IsOpen u2 ->u1 ∩ u2=∅ ∧ u1∪ u2=univ ->u1=∅ ∨ u2=∅) := by
    intro H u1 u2 h1 h2 
    simp only [IsConnected,IsPreconnected] at H
    replace H:=H.right _ _ h1.left h1.right (by rw [h2.right])
    simp at H; by_contra  hc; push_neg at hc
    let p1:=setNonemptyIff.mpr  hc.left
    let p2:=setNonemptyIff.mpr  hc.right
    exact (setNonemptyIff.mp (H p1 p2)) h2.left
  have mpr: (∀{u1 u2:Set α},IsOpen u1 ∧IsOpen u2 ->u1 ∩ u2=∅ ∧ u1∪ u2=univ ->u1=∅ ∨ u2=∅) 
  -> IsConnected (univ:Set α)  := by
    intro H; simp [IsConnected,IsPreconnected]
    intro u1 u2 hu1 hu2 hu1u2 hu1' hu2'
    by_contra hc; replace hc:=setNotNonemptyIff.mp hc
    replace H:=H ⟨hu1,hu2⟩ ⟨hc, subset_antisymm (by simp) hu1u2⟩ 
    cases' H with H1 H2
    · exact (setNotNonemptyIff.mpr H1) hu1'
    · exact (setNotNonemptyIff.mpr H2) hu2'
  exact ⟨mp,mpr⟩  

lemma connectedIffSubspaceConnected [TopologicalSpace α]{s:Set α} :
IsConnected s ↔ IsConnected (univ:Set (Subtype s))  := by 
  have mp: IsConnected s -> IsConnected (univ:Set (Subtype s)) := by
    intro h ; let inst1:=Subtype.connectedSpace  h
    exact @isConnected_univ _ _ inst1
  have mpr : IsConnected (univ:Set (Subtype s)) -> IsConnected s := by
    intro h ; simp [IsConnected,IsPreconnected] 
    let h':=h
    simp [IsConnected] at h
    have p1: Set.Nonempty s := by
      refine' Exists.elim h.left _
      intro x _
      exact ⟨_,x.property ⟩ 
    refine' ⟨p1,_⟩ 
    by_contra hc; push_neg at hc
    refine' Exists.elim hc _
    intro u1 hc
    refine' Exists.elim hc _
    intro u2 hc
    let u1':=PreIm(fun x:Subtype s=>x.val,u1)
    let u2':=PreIm(fun x:Subtype s=>x.val,u2)
    have pu1':IsOpen u1' := continuousDef.mp (subtypeValIsContinuous) hc.left
    have pu2':IsOpen u2' := continuousDef.mp (subtypeValIsContinuous) hc.right.left
    have p2: u1'∩ u2' =∅ := by
      by_contra hc2; replace hc2 :=setNonemptyIff.mpr hc2
      refine' Exists.elim hc2 _
      intro z' hz'; simp at hz'
      let p3:=hc.right.right.right.right.right; 
      replace p3:=setNotNonemptyIff.mp p3
      have p4: z'.val ∈ s ∩ (u1 ∩ u2) := by
        simp; exact hz'
      rw [p3] at p4; simp at p4
    have inst1:Nonempty (Subtype s) := by
      simp; exact p1
    have p3: univ ⊆ u1' ∪  u2' := by
      refine' setSubsetIff.mpr _
      intro x' _; 
      exact setSubsetIff.mp hc.right.right.left _  x'.property
    replace p3:=connectedDef.mp h' ⟨pu1',pu2'⟩  ⟨p2, subset_antisymm (by simp) p3⟩ 
    cases' p3 with p31 p32
    · refine' Exists.elim hc.right.right.right.left _
      intro y hy; simp at hy
      have p4: ⟨_,hy.left ⟩ ∈ u1' := by
        simp; exact hy.right
      rw [p31] at p4; simp at p4
    · refine' Exists.elim hc.right.right.right.right.left _
      intro y hy; simp at hy
      have p4: ⟨_,hy.left ⟩ ∈ u2' := by
        simp; exact hy.right
      rw [p32] at p4; simp at p4
  exact ⟨mp,mpr⟩ 

lemma connectedImageConnected [TopologicalSpace α] [TopologicalSpace β] {f:α->β}
(h1:Continuous f) (h2:IsConnected (univ:Set α)) : IsConnected (Im(f,univ)) := 
IsConnected.image h2 _ (Continuous.continuousOn h1)

lemma pathConnectedDef [TopologicalSpace α] {s:Set α} :
IsPathConnected s ↔ s.Nonempty∧(∀{x y:α},x∈ s∧ y∈ s ->∃ γ :Path x y, Im(γ,univ) ⊆ s) := by 
  have mp: IsPathConnected s -> 
  s.Nonempty∧ (∀{x y:α},x∈ s∧ y∈ s ->∃ γ :Path x y, Im(γ,univ) ⊆ s) := by
    intro h;  refine' ⟨(isPathConnected_iff.mp h).1,_ ⟩ 
    let p1:=(isPathConnected_iff.mp h).2
    intro x y h2; replace p1:= p1 _ h2.left _ h2.right
    simp [JoinedIn] at p1; refine' Exists.elim p1 _
    intro γ hγ ; refine' ⟨γ,setSubsetIff.mpr _ ⟩ 
    intro z hz
    refine' Exists.elim hz _
    intro  t ht; rw [ht.right.symm]
    exact hγ _ t.property
  have mpr:(s.Nonempty∧ (∀{x y:α},x∈ s∧ y∈ s ->∃ γ :Path x y, Im(γ,univ) ⊆ s))
  ->IsPathConnected s := by
    intro H; refine' isPathConnected_iff.mpr ⟨H.left,_ ⟩ 
    intro x hx y hy; simp [JoinedIn]
    refine' Exists.elim (H.right  ⟨hx,hy⟩) _
    intro γ hγ ; refine' ⟨γ,_ ⟩ 
    intro t ht
    exact setSubsetIff.mp hγ (γ ⟨_,ht⟩) (by simp)
  exact ⟨mp,mpr⟩ 

def pathMK [TopologicalSpace α] {x y:α}{γ:unitInterval ->α}
(hγ:Continuous γ)(hx:γ 0 = x)(hy:γ 1=y):Path x y := {
  toFun:=γ
  continuous_toFun:=hγ
  source':=hx
  target':=hy}
  
lemma pathConnectedImpliesConnected [TopologicalSpace α] {s:Set α} (h:IsPathConnected s):
IsConnected s := IsPathConnected.isConnected h

lemma pathConnectedImagePathConnected [TopologicalSpace α] [TopologicalSpace β] {f:α->β}
(h1:Continuous f) (h2:IsPathConnected (univ:Set α)) : IsPathConnected (Im(f,univ)) := 
IsPathConnected.image h2 h1










