import GradMath.Basic.Basic
import GradMath.Basic.Function
import GradMath.Basic.Countable
import Mathlib.Topology.Basic
import Mathlib.Topology.Bases
import GradMath.Basic.SUP_INF
import Mathlib.Topology.Sequences

noncomputable section

namespace PointSetTopology

open FUNCTION SET Set LIST FINSET Classical  NAT COUNTABLE

universe u_1 u_2 u_3
variable {α: Type u_1} {β :Type u_2} {γ:Type u_3}

lemma TopologicalSpaceEqIff {t t' : TopologicalSpace α} :
t = t' ↔ ∀ (s : Set α), t.IsOpen s ↔ t'.IsOpen s := 
TopologicalSpace.ext_iff

lemma emptyIsOpen  [TopologicalSpace α] :  IsOpen (∅:Set α)
:=isOpen_empty

lemma univIsOpen  [TopologicalSpace α] :  IsOpen (univ: Set α) 
:=isOpen_univ

lemma emptyIsClosed [TopologicalSpace α] : IsClosed (∅ :Set α)
:= isClosed_empty

lemma univIsClosed [TopologicalSpace α] : IsClosed (univ:Set α)
:= isClosed_univ

lemma openComplIsClosed [TopologicalSpace α] {s :Set α}: (IsOpen s) -> (IsClosed (sᶜ)) 
:= by
  intro h
  have p1:(sᶜ)ᶜ = s := by simp
  rw [p1.symm] at h
  replace h:=isOpen_compl_iff.mp h
  exact h

lemma closedComplIsOpen  [TopologicalSpace α] {s :Set α}: (IsClosed s) -> (IsOpen (sᶜ))
:= by simp

lemma openSUnion [TopologicalSpace α]{s:Set (Set α)}(h:∀{t:Set α},t∈s→IsOpen t) :
IsOpen (⋃₀ s) := isOpen_sUnion @h

lemma closedSInter [TopologicalSpace α]{s:Set (Set α)}(h:∀(t:Set α),t∈s→IsClosed t) : 
IsClosed (⋂₀ s) := by
  let p1:=@setComplSInter  _ s
  have p2: ∀{t:Set α},t∈ Im(compl,s)→IsOpen t := by
    intro t h1
    simp at h1
    refine' Exists.elim h1 _
    intro si h2
    exact h2.right ▸ closedComplIsOpen (h _ h2.left)
  replace h2:=openSUnion p2
  let p3:=p1.symm ▸ openComplIsClosed h2
  simp at p3
  exact p3

lemma openUnion {s1 s2:Set α}[TopologicalSpace α](h1:IsOpen s1)(h2:IsOpen s2) :
IsOpen (s1 ∪ s2) := IsOpen.union h1 h2

lemma closedInter {s1 s2:Set α}[TopologicalSpace α](h1:IsClosed s1)(h2:IsClosed s2) :
IsClosed (s1 ∩ s2) := IsClosed.inter h1 h2

lemma openInter {s1 s2:Set α}[ts:TopologicalSpace α](h1:IsOpen s1)(h2:IsOpen s2) :
IsOpen (s1 ∩ s2) := ts.isOpen_inter _ _ h1 h2

lemma closedUnion {s1 s2:Set α}[ts:TopologicalSpace α](h1:IsClosed s1)(h2:IsClosed s2) :
IsClosed  (s1 ∪ s2) := by
  replace h1:=closedComplIsOpen h1
  replace h2:=closedComplIsOpen h2
  let p1:= openInter h1 h2
  rw [setComplUnion.symm] at p1
  replace p1:=openComplIsClosed p1
  rw [setComplCompl] at p1
  exact p1

lemma finsetOpenInter {S:Finset (Set α)}[TopologicalSpace α](h:∀{si},si∈S->IsOpen si)
:IsOpen (⋂₀ S.toSet ) := by
  rw [(foldrInterEqSInter S).symm]
  let rec aux (L:List (Set α)) (h1:∀(si),si∈L->IsOpen si):
    IsOpen (L.foldr (.∩.) univ ) := by
    match L with
    |[] =>
      simp
    |si::l' =>
      simp; simp at h1
      let p1:=aux l' h1.right
      exact openInter h1.left p1
  have p1:∀(si),si∈S.toList->IsOpen si := by
    intro si h1
    simp at h1; exact h h1
  exact aux _ p1

lemma listOpenInter {l:List (Set α)} [TopologicalSpace α] (h:∀{si},si∈l->IsOpen si)
:IsOpen (l.foldr (.∩.) univ) := by
  set L := l with HH
  match L with 
  | [] =>  simp
  | a::L' =>
    simp 
    have p1: ∀{si},si∈L'->IsOpen si := by
      intro si h1
      have p2: si∈a::L' := by
        simp; exact Or.inr h1
      exact h p2
    let p2:=listOpenInter p1
    have p3:a∈a::L' := by simp
    replace p3:= h p3
    exact openInter p3 p2

lemma finsetClosedUnion {S:Finset (Set α)}[TopologicalSpace α](h:∀{si},si∈S->IsClosed si)
:IsClosed (⋃₀ S.toSet) := by
  rw [(foldrUnionEqSUnion S).symm]
  let rec aux (L:List (Set α)) (h1:∀(si),si∈L->IsClosed si):
    IsClosed (L.foldr (.∪.) ∅ ) := by
    match L with
    |[] =>
      simp
    |si::l' =>
      simp; simp at h1
      let p1:=aux l' h1.right
      exact closedUnion h1.left p1
  have p1:∀(si),si∈S.toList->IsClosed si := by
    intro si h1
    simp at h1; exact h h1
  exact aux _ p1 

lemma continuousDef  [TopologicalSpace α] [TopologicalSpace β] {f : α → β} : 
Continuous f ↔ ∀ {s : Set β}, IsOpen s → IsOpen (PreIm(f,s) ):=continuous_def 

lemma continuousDef'  [ts1:TopologicalSpace α] [ts2:TopologicalSpace β] {f : α → β} :
Continuous f ↔ ∀ {s : Set β}, IsClosed s → IsClosed (PreIm(f,s) ):=by
  have mp: Continuous f -> ∀ (s : Set β), IsClosed s → IsClosed (PreIm(f,s) ) := by
    intro h1 s h2
    replace h2:= (continuousDef.mp h1) 
      (closedComplIsOpen  h2)
    rw [preImCompl] at h2
    replace h2:= openComplIsClosed h2
    simp at h2 ; exact h2; 
  have mpr:(∀ {s : Set β}, IsClosed s → IsClosed (PreIm(f,s) ))-> Continuous f := by
    intro h1
    have h2:∀ {s : Set β}, IsOpen s → IsOpen (PreIm(f,s) ) := by
      intro s h3
      replace h3:= h1 (openComplIsClosed h3)
      rw [preImCompl] at h3
      replace h3:=closedComplIsOpen h3
      simp at h3; exact h3
    exact continuousDef.mpr h2
  exact ⟨mp,mpr⟩ 

lemma continuousComp  [TopologicalSpace γ] [TopologicalSpace β]
[TopologicalSpace α] {g:β->γ} {f:α->β} (h1:Continuous g) (h2:Continuous f) :
Continuous (g∘f) := Continuous.comp h1 h2

@[reducible]
def sequenceN (α: Type u_1) :(Type u_1) := Nat->α      

structure neighb [TopologicalSpace α] (x:α) where
  set: Set α
  property: x∈set ∧ (IsOpen set)

lemma memInteriorIff [TopologicalSpace α] {s:Set α} {x:α} :
x ∈ interior s ↔∃(u:neighb x),u.set ⊆s := by
  have mp:x ∈ interior s ->∃(u:neighb x),u.set ⊆s := by
    intro h
    replace h:=mem_interior.mp h
    refine' Exists.elim h _
    intro u' h2
    let u:neighb x := ⟨_,h2.right.right,h2.right.left⟩ 
    exact ⟨u,h2.left⟩ 
  have mpr:(∃(u:neighb x),u.set ⊆s )-> x ∈ interior s := by
    intro h
    have p1:∃(t:Set α), (t⊆ s)∧ IsOpen t ∧ x ∈ t := by
      refine' Exists.elim h _
      intro u h1
      exact ⟨_,h1,u.property.right,u.property.left ⟩ 
    exact mem_interior.mpr p1
  exact ⟨mp,mpr⟩ 

lemma memClosureIff [TopologicalSpace α] {s:Set α} {x:α} :
x ∈ closure s ↔ ∀(u:neighb x), ∃(y:α), y∈s ∧ y∈u.set := by
  have mp: x ∈ closure s -> ∀(u:neighb x), ∃(y:α), y∈s ∧ y∈u.set := by
    intro h u
    simp [closure] at h
    by_contra hc
    push_neg at hc
    let p1:=openComplIsClosed u.property.right
    have p2: s⊆(u.setᶜ) := by
      refine' setSubsetIff.mpr _
      intro z h1; simp
      exact hc _ h1
    replace h:=h _ p1 p2
    let p3:=u.property.left
    simp at h; exact h p3
  have mpr: (∀(u:neighb x),∃(y:α),y∈s∧y∈u.set) ->x∈closure s := by
    intro h ; simp [closure]
    intro t h2 h3
    by_contra hc; push_neg at hc
    have p1:x∈tᶜ := by simp; exact hc 
    let u:neighb x:=⟨_,p1, closedComplIsOpen h2⟩ 
    refine' Exists.elim (h u) _
    intro y h5
    let p2:=(setSubsetIff.mp h3) _ h5.left
    let p4:=h5.right; simp at p4
    exact p4 p2
  exact ⟨mp,mpr⟩ 

lemma interiorIsMaximal [TopologicalSpace α]{s t:Set α}(h1:t⊆s)(h2:IsOpen t) :
t ⊆ interior s := interior_maximal h1 h2

lemma interiorIsOpen [TopologicalSpace α] {s:Set α}: IsOpen (interior s):=
isOpen_interior

lemma openIffEqInterior [TopologicalSpace α] {s:Set α}: interior s = s ↔ IsOpen s
:=interior_eq_iff_isOpen

lemma closureIsMinimal [TopologicalSpace α]{s t:Set α}(h1:s⊆t)(h2:IsClosed t) :
closure s ⊆ t := closure_minimal h1 h2

lemma closureIsClosed [TopologicalSpace α] {s : Set α}:IsClosed (closure s) :=
isClosed_closure

lemma closedIffEqClosure [TopologicalSpace α]{s:Set α}:closure s = s ↔ IsClosed s
:=closure_eq_iff_isClosed

lemma interiorSubset [TopologicalSpace α]{s:Set α}:interior s ⊆ s :=interior_subset

lemma subsetClosure [TopologicalSpace α]{s:Set α}: s ⊆ closure s:= subset_closure

lemma openMpr [TopologicalSpace α]{s:Set α} (h:∀{x:α},x∈s -> ∃nb:neighb x, nb.set ⊆s)
:IsOpen s := by
  refine' openIffEqInterior.mp _
  refine' setEqMpr interiorSubset _
  refine' setSubsetIff.mpr _
  intro x h2
  refine' Exists.elim (h h2)  _
  intro nb h3
  exact (setSubsetIff.mp 
    (interiorIsMaximal h3 nb.property.right)) _ nb.property.left

@[simp]
def sequenceN.convergesTo (x:sequenceN α) [TopologicalSpace α] (y: α):=
∀(u:neighb y), (∃N:ℕ, (∀{n:ℕ},N≤n -> (x n)∈u.set ))

lemma continuSeqImageConverg [TopologicalSpace α][TopologicalSpace β] {f:α->β} {x0:α}
(h1:Continuous f) (x:sequenceN α) (h2:x.convergesTo x0): 
sequenceN.convergesTo (f∘x) (f x0) := by 
  simp [sequenceN.convergesTo]
  intro u
  have p1:IsOpen (PreIm(f,u.set)) 
    := (continuousDef.mp h1) u.property.right
  simp [sequenceN.convergesTo] at h2
  have p2: x0 ∈ (PreIm(f,u.set)) := by
    simp;exact u.property.left
  let n_x0:neighb x0 :=⟨_,p2,p1⟩ 
  refine' Exists.elim (h2 n_x0) _
  intro N h3
  simp at h3
  exact ⟨_,h3⟩ 

class HausdorffSpace (α) [TopologicalSpace α] where
property:∀{x y:α }, x≠y -> ∃ (u1:neighb x) (u2:neighb y), u1.set ∩ u2.set = ∅ 

lemma finsetClosedInHausdorff [ts:TopologicalSpace α] [h:HausdorffSpace α]
(S: Finset α) : IsClosed S.toSet := by 
  let rec aux {n:Nat}  (s: Finset α) (HH:n=s.card) : IsClosed s.toSet := by
    match n with
    |0 =>
      replace HH:= Finset.card_eq_zero.mp HH.symm
      rw [HH]; simp
    |.succ n' =>
      set L:=s.toList with HH2
      match L with
      |[] =>
        have p1:0<s.card:= calc 
          0 < n'.succ := by simp
          _ = s.card :=HH
        have p2:0=s.card := calc 
          0 = [].length := by simp
          _ = s.toList.length :=congrArg List.length HH2
          _ = s.card := by simp
        rw [p2.symm] at p1
        simp at p1
      |x::l' =>
        have p1:l'.Nodup := by
          refine' listNodupIff.mpr _
          intro i j h1 h2 h3
          replace h1:i+1<(x::l').length := calc 
            i+1 < l'.length+1 :=by simp [h1]
            _ = (x::l').length := by simp
          replace h2:j+1<(x::l').length := calc 
            j+1 < l'.length+1 :=by simp [h2]
            _ = (x::l').length := by simp
          rw [HH2] at h1 h2
          replace h3: i+1≠ j+1 := by simp [h3]
          let p2:= (listNodupIff.mp (finsetToListNodup s)) h1 h2 h3
          simp_rw [HH2.symm] at p2; simp at p2
          exact p2
        let s':Finset α := ⟨↑l',Multiset.coe_nodup.mpr p1⟩ 
        let set_x :Finset α := ⟨↑[x],(by simp) ⟩ 
        have p2:s = (set_x ∪ s') := by
          refine' Finset.ext_iff.mpr _
          intro z
          have mp: z ∈ s -> z ∈ set_x ∪ s' := by
            intro h1
            have p3:z ∈(x::l') := by 
              rw [HH2]; simp; exact h1
            simp at p3; simp; exact p3
          have mpr:z ∈ set_x ∪ s' -> z ∈ s := by
            intro h1
            simp at h1
            have p3: z ∈ s.toList := by
              rw [HH2.symm]; simp
              exact h1
            simp at p3; exact p3
          exact ⟨mp,mpr ⟩ 
        have p3:n'=s'.card := by 
          simp
          have p4:n'.succ = (x::l').length := by
            rw [HH2]; simp; exact HH
          simp at p4; exact p4
        let p4:= aux s' p3
        have p5:IsClosed set_x.toSet := by
          have p6:IsOpen (set_x.toSetᶜ) := by
            refine' openIffEqInterior.mp _
            refine' setEqMpr interiorSubset _
            refine' setSubsetIff.mpr _
            intro y h2 
            simp at h2; 
            refine' Exists.elim (h.property h2) _
            intro u1 h3
            refine' Exists.elim h3 _
            intro u2  h3
            refine' memInteriorIff.mpr _
            have p5: u1.set⊆ (↑set_x)ᶜ := by 
              refine' setSubsetIff.mpr _
              intro z h4; simp
              by_contra hc
              have p6:z∈ u1.set ∩ u2.set := by
                simp; exact ⟨h4,hc.symm ▸ u2.property.left⟩ 
              replace p6:(u1.set ∩ u2.set).Nonempty := by
                simp [Set.Nonempty]; exact ⟨_,p6⟩ 
              replace p6:=setNonemptyIff.mp p6
              exact p6 h3
            exact ⟨_,p5⟩ 
          replace p6:=openComplIsClosed p6; simp at p6
          exact p6
        let p6:=closedUnion p5 p4
        rw [p2]; simp; exact p6
  set n:=S.card with HH
  exact aux S HH

lemma limitUniqueInHausdorff {x:sequenceN α } {x0:α}[ts:TopologicalSpace α] 
[h1:HausdorffSpace α](h2:x.convergesTo x0): 
∀{x0':α}, (x.convergesTo x0') -> x0=x0' := by
  intro x0' h3
  by_contra hc
  refine' Exists.elim (h1.property hc) _
  intro u1 h4
  refine' Exists.elim h4 _
  intro u2 h4
  simp [sequenceN.convergesTo] at h2 h3
  replace h2 := h2 u1
  replace h3 := h3 u2
  refine' Exists.elim h2 _
  intro N1 h5
  refine' Exists.elim h3 _
  intro N2 h6
  let N:= N1⊔N2
  replace h5:=@h5 N (by simp)
  replace h6:=@h6 N (by simp)
  have p1:u1.set ∩ u2.set ≠ ∅  := by
    refine' setNonemptyIff.mp _
    simp [Set.Nonempty]
    exact ⟨_,h5,h6⟩ 
  simp at p1; exact p1 h4

def boundary [TopologicalSpace α] (s:Set α):= (closure s)\(interior s)

def memBoundaryIff [TopologicalSpace α] {s:Set α} {x:α}: 
x∈boundary s ↔ ∀ {nb:neighb x}, ∃ (y1 y2:α ), y1∈s∧y1∈nb.set∧y2∈sᶜ∧y2∈nb.set := by
  have mp: x∈boundary s -> ∀ {nb:neighb x}, 
  ∃(y1 y2:α ),y1∈s∧y1∈nb.set∧y2∈sᶜ∧y2∈nb.set := by
    intro h1 nb; simp only [boundary,setMemDiffIff] at h1
    refine' Exists.elim (memClosureIff.mp h1.left nb) _
    intro y1 hy1
    have p1: ∃y2, y2 ∈ sᶜ ∧ y2 ∈ nb.set := by
      by_contra hc1
      push_neg at hc1
      have p2: nb.set ⊆ s := by
        refine' setSubsetIff.mpr _
        intro z hz
        by_contra hc2
        have p3: z∈sᶜ := by simp; exact hc2
        exact (hc1 _ p3) hz
      let p3:=memInteriorIff.mpr ⟨nb,p2⟩ 
      exact h1.right p3
    refine' Exists.elim p1 _
    intro y2 hy2
    exact ⟨y1,y2,hy1.left,hy1.right,hy2 ⟩ 
  have mpr: (∀ {nb:neighb x},∃(y1 y2:α ),y1∈s∧y1∈nb.set∧y2∈sᶜ∧y2∈nb.set)
  -> x∈boundary s := by
    intro h1; simp only [boundary,setMemDiffIff]
    have p1: ∀(nb:neighb x), ∃(y:α), y∈s ∧ y∈nb.set := by
      intro nb 
      refine' Exists.elim (@h1 nb) _
      intro y1 h2
      refine' Exists.elim h2 _
      intro y2 h2
      exact ⟨_,h2.left,h2.right.left⟩ 
    replace p1:=memClosureIff.mpr p1
    have p2: ¬ x∈interior s  := by
      by_contra hc
      simp [interior] at hc
      refine' Exists.elim hc _
      intro t ht
      replace h1:=@h1 ⟨_,ht.right,ht.left.left⟩ 
      refine' Exists.elim h1 _
      intro y1 h1
      refine' Exists.elim h1 _
      intro y2 h1; simp at h1
      exact h1.right.right.left 
        (setSubsetIff.mp ht.left.right _ h1.right.right.right)
    exact ⟨p1,p2⟩ 
  exact ⟨mp,mpr⟩ 

structure topologicalBasis (ts:TopologicalSpace α) where
  sets: Set (Set α )
  sets_forall_open : ∀{s: Set α}, (s∈sets) -> IsOpen s
  any_open_is_sunion: ∀{s:Set α}, (IsOpen s) -> ∃ (t:Set (Set α)), (t⊆sets)∧s=⋃₀t
/-
The parameter for a topologicalBasis is defined to be the topological space itself instead of its type is because it is possible to run into the case where there are multiple topological space structures on one set. 

-/

lemma basisForSomeSpaceIff (s:Set (Set α)):
(⋃₀s = univ) ∧ (∀{B1 B2:Set α}, B1∈s -> B2∈s-> 
(∀{x:α },x∈B1∩B2->∃(B3:Set α), (B3∈s)∧(x∈B3)∧(B3⊆B1∩B2))) ↔ 
∃! (ts:TopologicalSpace α), (∃(B:topologicalBasis ts),s=B.sets) := by
  have mp : ((⋃₀s = univ) ∧ (∀{B1 B2:Set α}, B1∈s -> B2∈s-> 
  (∀{x:α },x∈B1∩B2->∃(B3:Set α), (B3∈s)∧(x∈B3)∧(B3⊆B1∩B2)))) ->
  ∃! (ts:TopologicalSpace α), (∃(B:topologicalBasis ts),s=B.sets) := by
    simp [ExistsUnique]
    intro h1 h2
    let is_open (t :Set α) := 
      ∃(b:Set (Set α)), (b⊆s) ∧ (t = ⋃₀ b) 
    have is_open_univ : is_open univ := by 
      simp; have p1: s⊆s := by rfl
      exact ⟨_,p1,h1.symm⟩ 
    have is_open_inter : ∀(t1 t2:Set α), (is_open t1)->(is_open t2)
    -> is_open (t1 ∩ t2) := by
      intro t1 t2 t1h t2h
      let b:Set (Set α ) := {s'∈s | s' ⊆ t1 ∩ t2 }
      set sb:= ⋃₀ b with HH1
      have p1: is_open sb := by 
        have p2: b ⊆ s := by 
          refine' setSubsetIff.mpr _
          intro x' h3
          simp at h3; exact (h3.left.left)
        exact ⟨_,p2,HH1⟩ 
      have p2: sb = (t1 ∩ t2) := by
        refine' setEqIff.mpr _
        intro x' 
        have mp':x' ∈ sb -> x' ∈ t1 ∩ t2 := by
          intro h3; simp at h3
          refine' Exists.elim h3 _
          intro t h3
          let p3:=(setSubsetIff.mp h3.left.left.right) _ h3.right
          let p4:=(setSubsetIff.mp h3.left.right.right) _ h3.right
          simp; exact ⟨p3,p4⟩ 
        have mpr': x' ∈ t1 ∩ t2 -> x' ∈ sb := by
          intro h3; simp at t1h t2h
          refine' Exists.elim t1h _
          intro b1 t1h
          refine' Exists.elim t2h _
          intro b2 t2h
          have h3_1:=h3.left; have h3_2:=h3.right
          rw [t1h.right] at h3_1; simp at h3_1
          rw [t2h.right] at h3_2; simp at h3_2
          refine' Exists.elim h3_1 _
          intro r1 h3_1
          refine' Exists.elim h3_2 _
          intro r2 h3_2
          let p3:=(setSubsetIff.mp t1h.left) _ h3_1.left
          let p4:=(setSubsetIff.mp t2h.left) _ h3_2.left
          let p2:=h2 p3 p4 h3_1.right h3_2.right
          refine' Exists.elim p2 _
          intro B3 h4
          have p5:B3 ∈ b := by
            simp
            have p6': r1 ⊆ t1 := by
              refine' setSubsetIff.mpr _
              intro z h5; rw [t1h.right]
              simp; exact ⟨_,h3_1.left,h5⟩ 
            have p6 := calc 
              B3 ⊆ r1 := h4.right.right.left
              _ ⊆ t1  := p6'
            have p7':r2 ⊆ t2 := by
              refine' setSubsetIff.mpr _
              intro z h5; rw [t2h.right]
              simp; exact ⟨_,h3_2.left,h5⟩                        
            have p7:= calc 
              B3 ⊆ r2 := h4.right.right.right
              _ ⊆ t2 := p7'
            exact ⟨⟨h4.left,p6 ⟩,h4.left, p7⟩ 
          refine' setMemSUnionIff.mpr _
          exact ⟨_,p5,h4.right.left ⟩ 
        exact ⟨mp',mpr'⟩ 
      rw [p2.symm]; exact p1
    have is_open_sunion: ∀ (s':Set (Set α)), (∀(t:Set α), t∈s' →is_open t) 
    →is_open (⋃₀ s') := by
      intro s' h3
      let s'b := Im( fun (t:Subtype s')=>Classical.choose (h3 _ t.property) ,univ)
      have p1:⋃₀ s' =⋃₀ (⋃₀ s'b) := by
        refine' setEqIff.mpr _
        intro x 
        have mp: x ∈ ⋃₀ s' -> x ∈ ⋃₀ ⋃₀ s'b := by
          intro h4; simp; simp at h4
          refine' Exists.elim h4 _
          intro t h4
          let p4:=h3 _ h4.left
          let p2:=Classical.choose_spec p4
          let p3:=h4.right; rw [p2.right] at p3
          simp at p3
          refine' Exists.elim p3 _
          intro t_1 p3
          refine' ⟨_,_,p3.right⟩ 
          refine' ⟨t,h4.left,p3.left⟩ 
        have mpr: x ∈ ⋃₀ ⋃₀ s'b ->  x ∈ ⋃₀ s' := by
          intro h4; simp ;simp at h4
          refine' Exists.elim h4 _
          intro t h4
          refine' Exists.elim h4.left _
          intro t_1 h5
          refine' Exists.elim h5 _
          intro h5 h6
          let p2:=h3 _ h5
          refine' ⟨_,h5,_⟩ 
          let p3:=Classical.choose_spec p2
          rw [p3.right]; simp
          exact ⟨_,h6,h4.right⟩ 
        exact ⟨mp,mpr⟩ 
      have p2:(⋃₀ s'b) ⊆ s := by
        refine' setSubsetIff.mpr _
        intro t h4; simp at h4
        refine' Exists.elim h4 _
        intro r h4
        refine' Exists.elim h4 _
        intro h4 h5
        let p1:=h3 _ h4
        let p2:=Classical.choose_spec p1
        exact (setSubsetIff.mp p2.left) _ h5
      exact ⟨_,p2,p1⟩ 
    let ts:TopologicalSpace α:=
      ⟨is_open,is_open_univ,is_open_inter,is_open_sunion⟩ 
    let tb:topologicalBasis ts:={
      sets :=s
      sets_forall_open := by
        intro s1 h3; 
        let b:=[s1].toFinset.toSet
        have p1: b⊆s := by
          refine' setSubsetIff.mpr _
          intro s1' h4
          simp at h4; rw [h4]; exact h3
        have p2: s1=⋃₀ b := by
          rw [← foldrUnionEqSUnion]
          simp
        exact ⟨_,p1,p2⟩ 
      any_open_is_sunion := by
        intro s1 h3; exact h3}
    have p1:s=tb.sets := by rfl
    refine' ⟨ts,⟨_,p1⟩ ,_⟩ 
    intro ts' tb' h4
    refine' TopologicalSpaceEqIff.mpr _
    intro s1
    rw [p1] at h4
    have mpr:ts.IsOpen s1 -> ts'.IsOpen s1 := by
      intro h5
      let p2:=tb.any_open_is_sunion h5
      rw [h4] at p2;
      refine' Exists.elim p2 _
      intro b h6
      rw [h6.right]
      refine' openSUnion _
      intro t1 h7
      exact tb'.sets_forall_open ((setSubsetIff.mp h6.left) _ h7)
    have mp: ts'.IsOpen s1 -> ts.IsOpen s1 := by
      intro h5
      let p2:=tb'.any_open_is_sunion h5
      rw [h4.symm] at p2
      simp [IsOpen]; exact p2
    exact ⟨mp,mpr⟩ 
  have mpr:(∃! (ts:TopologicalSpace α), (∃(B:topologicalBasis ts),s=B.sets)) ->
  ((⋃₀s = univ) ∧ (∀{B1 B2:Set α}, B1∈s -> B2∈s-> 
  (∀{x:α },x∈B1∩B2->∃(B3:Set α), (B3∈s)∧(x∈B3)∧(B3⊆B1∩B2))))  := by
    intro h; simp [ExistsUnique] at h 
    refine' Exists.elim h _
    intro ts h
    refine' Exists.elim h.left _
    intro tb h1
    let p1:=tb.any_open_is_sunion univIsOpen
    have p2: ⋃₀ s = univ  := by
      refine' Exists.elim p1 _
      intro b h2; 
      refine' setEqIff.mpr _
      intro x
      have mp: x ∈ ⋃₀ s -> x ∈ univ := by simp
      have mpr : x ∈ univ -> x ∈ ⋃₀ s := by
        intro h3; simp
        rw [h2.right] at h3
        simp at h3
        refine' Exists.elim h3 _
        intro t h4
        have p1: t ∈tb.sets := setSubsetIff.mp h2.left _ h4.left
        rw [h1.symm] at p1
        exact ⟨_,p1,h4.right⟩ 
      exact ⟨mp,mpr⟩ 
    have p3:∀{B1 B2:Set α}, B1∈s → B2∈s → ∀{x:α}, x∈ B1∩B2 → 
      ∃B3, B3∈s ∧ x∈B3 ∧ B3⊆(B1∩B2) := by
      intro B1 B2 B1h B2h x h3 
      rw [h1] at B1h B2h
      let p3:=tb.sets_forall_open B1h
      let p4:=tb.sets_forall_open B2h
      refine' Exists.elim 
        (tb.any_open_is_sunion (openInter p3 p4)) _
      intro b h4; rw [h4.right] at h3
      simp at h3
      refine' Exists.elim h3 _
      intro B3 h5; rw [h1.symm] at h4
      let p5:=(setSubsetIff.mp h4.left) _ h5.left
      have p6: B3 ⊆ B1 ∩ B2 := by
        rw [h4.right]; 
        refine' setSubsetIff.mpr _
        intro y h6; simp
        exact ⟨_,h5.left,h6⟩ 
      exact ⟨_,p5,h5.right,p6⟩ 
    exact ⟨p2,p3⟩ 
  exact ⟨mp,mpr⟩ 

structure neighbBasis [ts:TopologicalSpace α] (x:α) where
  neighbs: Set (neighb x )
  exists_contained: ∀(nb:neighb x), ∃ (t:neighb x), t∈neighbs ∧ t.set⊆nb.set

lemma neighbBasisNonempty {x:α} [ts:TopologicalSpace α] {nbB:neighbBasis x}:
nbB.neighbs.Nonempty := by
  simp only [Set.Nonempty]
  refine' Exists.elim (nbB.exists_contained ⟨ univ,by simp ⟩ ) _ 
  intro nb hnb
  exact ⟨ _,hnb.left⟩ 

class fstCountable (α) [TopologicalSpace α] where
property:∀(x:α), ∃nbB: neighbBasis x, atMostCountable nbB.neighbs

class sndCountable (α) [ts:TopologicalSpace α] where
property:∃(tb:topologicalBasis ts), atMostCountable tb.sets

lemma existsNestedNeighbBasis [ts:TopologicalSpace α] [fstCountable α] :
∀(x:α), ∃nbB: neighbBasis x, (∃f:Nat -> neighb x, nbB.neighbs = Im(f,univ) ∧ 
(∀(n:ℕ), (f (n+1)).set ⊆ (f n).set)) := by 
  intro x 
  refine' Exists.elim (fstCountable.property x) _
  intro nbB' h1
  simp only [atMostCountable] at h1
  refine' Exists.elim h1 _
  intro g hg
  let f: ℕ -> Set α  := fun n =>
    ((List.range (n+1)).map (neighb.set∘g)).foldr (.∩.) univ
  have p1: ∀(n:ℕ), IsOpen (f n) := by
    intro n; simp
    have p2: ∀{t:Set α}, (t∈((List.range (n+1)).map (neighb.set∘g))) -> IsOpen t := by
      intro t ht
      refine' Exists.elim (listMemIff.mp ht) _
      intro k hk1
      refine' Exists.elim hk1 _ 
      intro hk1 hk2
      simp at hk2; rw [hk2.symm]
      exact (g k).property.right
    exact listOpenInter p2
  have p2: ∀(n:ℕ), f (n+1) ⊆ f n := by
    intro n ;simp; 
    have hcomm:Commutative (fun (x y:Set α)=> x ∩ y) := inter_comm
    have hassoc: Associative (fun (x y:Set α)=> x ∩ y) := inter_assoc
    let p3:=List.foldl_eq_foldr hcomm hassoc
    rw [←p3,←p3,List.range_succ]
    simp
  let rec p3:∀(n:ℕ), x∈ (f n) := by
    intro n; simp
    match n with
    | 0 => simp; exact (g 0).property.left
    | .succ n =>
      have hcomm:Commutative (fun (x y:Set α)=> x ∩ y) := inter_comm
      have hassoc: Associative (fun (x y:Set α)=> x ∩ y) := inter_assoc
      let p4:=List.foldl_eq_foldr hcomm hassoc
      rw [←p4,List.range_succ]; simp
      let p5:=p3 n; simp_rw [←p4] at p5
      exact ⟨p5, (g (n+1)).property.left ⟩ 
  let G:ℕ ->neighb x :=fun n=> ⟨f n, p3 n,p1 n⟩ 
  let nbB: neighbBasis  x :={
    neighbs:=Im(G,univ) 
    exists_contained := by
      intro nb
      refine' Exists.elim (nbB'.exists_contained nb) _
      intro t ht
      rw [hg] at ht; simp at ht
      refine' Exists.elim ht.left _
      intro n hn
      have p3: (f n) ⊆ t.set := by
        rw [hn.symm]
        match n with
        | 0 => simp;rfl
        | .succ n' =>
          simp
          have hcomm:Commutative (fun (x y:Set α)=> x ∩ y) := inter_comm
          have hassoc: Associative (fun (x y:Set α)=> x ∩ y) := inter_assoc
          let p3:=List.foldl_eq_foldr hcomm hassoc
          rw [←p3,List.range_succ,List.map_append,List.foldl_append]
          simp only [List.map,List.foldl]; simp
      refine' ⟨G n,(by simp),subset_trans p3 ht.right⟩ }
  refine' ⟨nbB,G,rfl,p2⟩ 

lemma memClosureFstCountableIff [ts:TopologicalSpace α] [fstCountable α] {x:α} {s:Set α} :
x∈ closure s ↔ ∃ (a:sequenceN α), Im(a,univ)⊆s ∧ a.convergesTo x := by 
  have mp:  x∈ closure s -> ∃ (a:sequenceN α), Im(a,univ)⊆s ∧ a.convergesTo x := by
    intro h1
    refine' Exists.elim (existsNestedNeighbBasis x ) _
    intro nbB hnbB
    refine' Exists.elim  hnbB  _
    intro f hf
    let a:sequenceN α:= 
      fun n =>choose (memClosureIff.mp h1 (f n))
    refine' ⟨a,_⟩ 
    have p1: Im(a,univ) ⊆ s := by
      refine' setSubsetIff.mpr _
      intro z hz
      simp at hz
      refine' Exists.elim hz _
      intro n hn
      let p2:=choose_spec (memClosureIff.mp h1 (f n))
      rw [hn] at p2; exact p2.left
    have p2:a.convergesTo x := by
      simp [sequenceN.convergesTo]
      intro nb_given
      refine' Exists.elim (nbB.exists_contained nb_given) _
      intro nb2 hnb2
      let p3:=hnb2.left; rw [hf.left] at p3
      simp only [mem_image] at p3
      refine' Exists.elim p3 _
      intro N hN; refine' ⟨N,_⟩ 
      intro n hn 
      refine' setSubsetIff.mp hnb2.right _ _
      let rec p4 m (hm:N≤m): (f m).set ⊆ (f N).set := by
        have p5:m = N+ (m-N) := calc 
          m = m-N+N  :=(natSubtractAdd hm).symm
          _ = N+ (m-N) := add_comm _ _
        rw [p5]; set K:=m-N
        match K with
        | 0 =>  rw [Nat.add_zero]
        | .succ k' =>
          let p6:= p4 _ ((by simp):N≤N+k') 
          rw [Nat.succ_eq_add_one,← Nat.add_assoc]
          calc 
            _ ⊆ _:=hf.right (N+k')
            _ ⊆ _ :=p6
      rw [hN.right.symm]
      refine' setSubsetIff.mp (p4 _ hn) _ _
      exact (choose_spec (memClosureIff.mp h1 (f n))).right
    exact ⟨p1,p2⟩ 
  have mpr:(∃ (a:sequenceN α), Im(a,univ)⊆s ∧ a.convergesTo x)->x∈ closure s := by
    intro h1
    refine' memClosureIff.mpr _
    simp only [sequenceN.convergesTo] at h1
    intro nb
    refine' Exists.elim h1 _
    intro a ha 
    refine' Exists.elim (ha.right nb) _
    intro N hN
    replace hN :=@hN N (by simp)
    have p1: a N ∈ s := by
      refine' setSubsetIff.mpr (ha.left) _
      simp
    exact ⟨_,p1,hN⟩ 
  exact ⟨mp,mpr⟩ 

lemma memInteriorFstCountableIff [ts:TopologicalSpace α] [fstCountable α] {x:α} {s:Set α} :
x∈interior s ↔∀{a:sequenceN α},(a.convergesTo x) -> ∃(N:ℕ),∀{n},N≤n-> a N∈s := by
  have mp: x∈interior s ->∀{a:sequenceN α},(a.convergesTo x) ->
  ∃(N:ℕ),∀{n},N≤n-> a N∈s  := by
    intro h1 a ha; by_contra hc
    push_neg at hc; simp at hc
    replace hc: ∀ (n: ℕ), a n ∉ s := by
      intro n; exact (hc n).right
    have p1: Im(a,univ)⊆sᶜ := by
      refine' setSubsetIff.mpr _
      intro y  hy; simp only [mem_image] at hy
      refine' Exists.elim hy _
      intro n hn; rw [hn.right.symm]
      simp; exact hc n
    let p2:=memClosureFstCountableIff.mpr ⟨_,p1,ha⟩ 
    refine' Exists.elim (memInteriorIff.mp h1) _
    intro nb hnb
    refine' Exists.elim (memClosureIff.mp p2 nb) _
    intro z hz; simp at hz
    exact hz.left (setSubsetIff.mp hnb z hz.right)
  have mpr: (∀{a:sequenceN α},(a.convergesTo x) -> ∃(N:ℕ),∀{n},N≤n-> a N∈s)
  -> x∈interior s := by 
    intro h1
    refine' memInteriorIff.mpr _
    by_contra hc; push_neg at hc
    refine' Exists.elim (existsNestedNeighbBasis x) _
    intro nbB hnbB
    refine' Exists.elim (hnbB) _
    intro f hf
    replace hc: ∀ (u : neighb x), ∃(y:α), y∈u.set∧y∉s := by
      intro nb
      refine' Exists.elim (not_subset.mp (hc nb)) _
      intro an han
      exact ⟨_,han⟩ 
    let a:sequenceN α := 
      fun n => choose (hc ( f n))
    have ha:∀(n:Nat), (a n)∈(f n).set ∧ (a n)∉s := by
      intro n 
      exact choose_spec (hc ( f n))
    have p1:a.convergesTo x := by
      simp [sequenceN.convergesTo]
      intro nb
      refine' Exists.elim (nbB.exists_contained nb) _
      intro nb2 hnb2
      let p2:=hf.left ▸ hnb2.left
      simp only [mem_image] at p2
      refine' Exists.elim p2 _
      intro N hN; refine' ⟨N,_⟩ 
      intro n hn
      refine' setSubsetIff.mp hnb2.right _ _
      let rec p3 m (hm:N≤m): (f m).set ⊆ (f N).set := by
        have p5:m = N+ (m-N) := calc 
          m = m-N+N  :=(natSubtractAdd hm).symm
          _ = N+ (m-N) := add_comm _ _
        rw [p5]; set K:=m-N
        match K with
        | 0 =>  rw [Nat.add_zero]
        | .succ k' =>
          let p6:= p3 _ ((by simp):N≤N+k') 
          rw [Nat.succ_eq_add_one,← Nat.add_assoc]
          calc 
            _ ⊆ _:=hf.right (N+k')
            _ ⊆ _ :=p6
      rw [hN.right.symm]
      exact setSubsetIff.mp (p3 _ hn) _ (ha n).left
    refine' Exists.elim (h1 p1) _
    intro N hN
    exact (ha N).right (@hN N (by simp) )
  exact ⟨mp,mpr⟩ 

@[reducible]
instance {α} [ts:TopologicalSpace α] [sc:sndCountable α]:
fstCountable α  := by
  have p1:∀(x:α), ∃nbB: neighbBasis x, atMostCountable nbB.neighbs := by
    intro x 
    refine' Exists.elim sc.property _
    intro tB htB
    let b':Set (Set α) := fun s => x∈s ∧ s∈tB.sets
    let b:Set (neighb x):=Im( fun t => 
      ⟨t.val,(mem_def.mp t.property).left,
      tB.sets_forall_open (mem_def.mp t.property).right⟩,
      (univ: Set (Subtype b')))
    have p1:b' ⊆ tB.sets := by
      refine' setSubsetIff.mpr _
      intro t ht; simp [mem_def] at ht
      exact ht.right
    have p2: b'.Nonempty := by
      simp [Set.Nonempty]
      refine' Exists.elim (tB.any_open_is_sunion univIsOpen) _
      intro ss hss
      have p3: x∈ ⋃₀ ss := by
        rw [hss.right.symm]; simp
      simp at p3
      refine' Exists.elim p3 _
      intro t ht
      exact ⟨t,ht.right,setSubsetIff.mp hss.left _ ht.left ⟩ 
    replace p1:=subsetOfCountable p2 p1 htB
    let nbB:neighbBasis x := {
      neighbs:=b
      exists_contained:=by
        intro nb_give
        refine' Exists.elim 
          (tB.any_open_is_sunion nb_give.property.right) _
        intro ss hss
        let p3:=hss.right ▸ nb_give.property.left
        simp at p3
        refine' Exists.elim p3 _
        intro t ht;
        let t':neighb x:= 
          ⟨t,ht.right,tB.sets_forall_open (setSubsetIff.mp hss.left _ ht.left)⟩ 
        refine' ⟨t',_ ⟩ 
        have p4: t' ∈ b := by
          simp; exact ⟨ht.right,(setSubsetIff.mp hss.left _ ht.left) ⟩ 
        have p5: t'.set ⊆ nb_give.set := by
          refine' setSubsetIff.mpr _
          intro y hy; simp at hy
          rw [hss.right]; simp
          exact ⟨_,ht.left,hy ⟩ 
        exact ⟨p4,p5⟩ }
    refine' ⟨nbB,_ ⟩ 
    exact imageOfCountable _ (subtypeIsCountable p1)
  exact ⟨p1⟩ 

lemma existsCountableDenseSubsetInSnd {α} [h0:Nonempty α] [ts:TopologicalSpace α] [sc:sndCountable α]:
∃(s:Set α), s.atMostCountable ∧ Dense s := by 
  refine' Exists.elim sc.property _
  intro tB htB; 
  let tBsets' := tB.sets \ {∅}
  have p1:tBsets' ⊆ tB.sets := by simp
  have p2:tBsets'.Nonempty := by
    simp [Set.Nonempty]
    refine' Exists.elim (tB.any_open_is_sunion univIsOpen) _
    intro B hB; 
    match h0 with
    | .intro a =>
      have p3: a∈⋃₀ B := by
        rw [hB.right.symm]; simp
      simp at p3
      refine' Exists.elim p3 _
      intro t ht
      have p4: ¬t = ∅ := by
        refine' setNonemptyIff.mp _
        simp [Set.Nonempty]
        exact ⟨_,ht.right⟩ 
      exact ⟨_,setSubsetIff.mp hB.left _ ht.left,p4 ⟩ 
  replace p2:=subsetOfCountable p2 p1 htB
  simp only [atMostCountable] at p2
  refine' Exists.elim p2 _
  intro f hf
  have p3: ∀(n:ℕ), (f n).Nonempty := by
    intro n; 
    have p4: f n ∈ tB.sets \ {∅} := by
      rw [hf]; simp
    replace p4:=(setMemDiffIff.mp p4).right
    simp at p4; exact setNonemptyIff.mpr p4
  let g:ℕ->α := 
    fun n =>choose (p3 n)
  refine' ⟨Im(g,univ), imageOfCountable _ NIsCountable, _⟩ 
  have p4:∀(x:α), x∈ closure (Im(g,univ)) := by
    intro x; refine' memClosureIff.mpr _
    intro nb
    refine' Exists.elim (tB.any_open_is_sunion nb.property.right) _
    intro B hB
    let p5:=hB.right ▸ nb.property.left
    simp at p5
    refine' Exists.elim p5 _
    intro t ht
    have p6:t∈ Im(f,univ) := by
      rw [hf.symm]; refine' setMemDiffIff.mpr _
      refine' ⟨setSubsetIff.mp hB.left _ ht.left,_ ⟩ 
      simp; refine' setNonemptyIff.mp _
      simp only [Set.Nonempty]; exact ⟨_,ht.right⟩ 
    simp at p6; refine' Exists.elim p6 _
    intro n hn; 
    refine' ⟨g n,(by simp) ,_ ⟩ 
    have p8: t ⊆  nb.set := by
      refine' setSubsetIff.mpr _
      intro z hz; rw [hB.right]
      simp; exact ⟨_,ht.left,hz⟩ 
    have p7: g n ∈ t := by
      rw [hn.symm]; exact choose_spec (p3 n)
    simp; exact setSubsetIff.mp p8 _ p7
  exact p4

structure openCover (s:Set α) [TopologicalSpace α] where
sets : Set (Set α )
sets_forall_open : ∀{s: Set α}, (s∈sets) -> IsOpen s
is_covered: s⊆⋃₀ sets

structure closedCover (s:Set α) [TopologicalSpace α] where
sets : Set (Set α )
sets_forall_closed : ∀{s: Set α}, (s∈sets) -> IsClosed s
is_covered: s⊆⋃₀ sets

lemma existsCountableSubcoverInSnd  {α} [h0:Nonempty α] [ts:TopologicalSpace α] [sc:sndCountable α]
(cover:openCover (univ:Set α)): ∃(cover':openCover (univ:Set α)), 
cover'.sets.atMostCountable∧cover'.sets⊆ cover.sets:= by
  refine' Exists.elim sc.property _
  intro tB ftB
  let tB'' := {t'∈tB.sets|∃(t:Set α),t∈cover.sets∧t'⊆t}
  have p1:tB'' ⊆ tB.sets := by simp
  have p2:tB''.Nonempty := by
    simp [Set.Nonempty]; 
    match h0 with
    | .intro a => 
      have p3: a∈univ := by simp
      replace p3:=setSubsetIff.mp cover.is_covered _ p3
      simp at p3
      refine' Exists.elim p3 _
      intro t ht
      refine' Exists.elim (tB.any_open_is_sunion (cover.sets_forall_open ht.left)) _
      intro b hb 
      refine' Exists.elim (setMemSUnionIff.mp (hb.right ▸ ht.right)) _
      intro t' ht' 
      refine' ⟨_,setSubsetIff.mp hb.left _ ht'.left,_,ht.left,_ ⟩ 
      refine' setSubsetIff.mpr _
      intro z hz; rw [hb.right]; refine' setMemSUnionIff.mpr _
      exact ⟨_,ht'.left,hz ⟩ 
  replace p2:=subsetOfCountable p2 p1 ftB
  let f:=fun (x:(Subtype tB'')) => (choose (mem_def.mp x.property).right)
  let tB':=Im(f, (univ:Set (Subtype tB'')))
  have p3:tB'.atMostCountable := imageOfCountable _ (subtypeIsCountable p2)
  let cover' :openCover (univ:Set α) := {
    sets:=tB'
    sets_forall_open := by
      intro t ht; simp only [mem_image] at ht
      refine' Exists.elim ht _
      intro s hs; rw [hs.right.symm]
      exact cover.sets_forall_open (choose_spec (mem_def.mp s.property).right).left
    is_covered := by
      refine' setSubsetIff.mpr _; intro z hz; 
      replace hz:=setMemSUnionIff.mp (setSubsetIff.mp cover.is_covered _ hz)
      refine' setMemSUnionIff.mpr _
      refine' Exists.elim hz _
      intro t ht
      refine' Exists.elim (tB.any_open_is_sunion (cover.sets_forall_open ht.left)) _
      intro b hb; 
      refine' Exists.elim (setMemSUnionIff.mp (hb.right ▸ ht.right)) _
      intro t'' ht''
      have p4:t''∈ tB'' :=by
        simp
        have p5: t''⊆t := by
          refine' setSubsetIff.mpr _
          intro y hy; rw [hb.right]
          simp; exact ⟨_,ht''.left,hy⟩ 
        exact ⟨setSubsetIff.mp hb.left _ ht''.left, _,ht.left,p5 ⟩ 
      let t''coe:Subtype tB'' := ⟨t'',p4 ⟩ 
      let pt':=choose_spec (mem_def.mp t''coe.property).right
      have p5: f t''coe ∈ Im(f,univ) := by
        refine' (mem_image f univ (f t''coe)).mpr _
        exact ⟨t''coe,(by simp) ⟩ 
      exact ⟨ _,p5,setSubsetIff.mp pt'.right _ ht''.right⟩  }
  refine' ⟨cover', p3,setSubsetIff.mpr _⟩ 
  intro a ha; refine' Exists.elim ha _
  intro s hs; simp at hs
  let p4:=(choose_spec (mem_def.mp s.property).right)
  rw [hs.symm]; exact p4.left

end PointSetTopology

namespace CoeMathlib

open FUNCTION SET Set LIST FINSET Classical  NAT COUNTABLE PointSetTopology

universe u_1

variable {α :Type u_1}

def fstCountableToFirstCountableTopology  [TopologicalSpace α] (inst:fstCountable α):
TopologicalSpace.FirstCountableTopology α  := by 
  have p1: ∀ (a : α), (nhds a).IsCountablyGenerated := by
    intro a
    refine' Exists.elim (inst.property a) _
    intro nbB hnbB
    let s:=Im(neighb.set,nbB.neighbs)
    have p2: s.Countable := by
      refine' Set.countable_iff_exists_subset_range.mpr _
      refine' Exists.elim hnbB _
      intro f hf; refine' ⟨fun n =>(f n).set,_ ⟩ 
      refine' setSubsetIff.mpr _
      intro t ht; simp at ht
      refine' Exists.elim ht _
      intro nb hnb; rw [hnb.right.symm]
      rw [hf] at hnb; simp at hnb
      simp [range]
      refine' Exists.elim hnb.left _
      intro n hn; replace hn:= congrArg neighb.set hn
      exact ⟨_,hn ⟩ 
    refine' ⟨_,p2,_ ⟩ ; 
    have p3: (nhds a).sets = (Filter.generate s).sets := by
      refine' setEqIff.mpr _
      intro t 
      have mp:t ∈ (nhds a).sets ->t ∈ (Filter.generate s).sets := by
        intro h1; replace h1:=mem_nhds_iff.mp h1
        refine' Exists.elim h1 _
        intro t2 ht2
        refine' Filter.mem_generate_iff.mpr _
        refine' Exists.elim (nbB.exists_contained ⟨_,ht2.right.right,ht2.right.left ⟩ ) _
        intro t3 ht3; simp at ht3
        have p4:{t3.set}⊆ s := by 
          simp; exact ⟨_,ht3.left,rfl ⟩ 
        refine' ⟨{t3.set},p4,by simp,_ ⟩ 
        simp; exact (subset_trans ht3.right ht2.left)
      have mpr:t ∈ (Filter.generate s).sets -> t ∈ (nhds a).sets := by
        intro h1; replace h1:=Filter.mem_generate_iff.mp h1
        refine' mem_nhds_iff.mpr _
        refine' Exists.elim h1 _
        intro b h1
        refine' Exists.elim h1 _
        intro hb h1
        let b':=h1.left.toFinset
        have p4:b'.toSet = b := by simp
        rw [p4.symm] at hb
        have p5:(∀ {si : Set α}, si ∈ b' → IsOpen si) := by
          intro si hsi; replace hsi:=setSubsetIff.mp hb _ hsi
          simp at hsi; refine' Exists.elim hsi _
          intro nb hnb; rw [hnb.right.symm]; exact nb.property.right
        replace p5:=finsetOpenInter p5
        have p6:⋂₀ b'.toSet = ⋂₀ b := by simp
        rw [p6] at p5
        have p7:a∈ ⋂₀ b := by
          simp; intro t ht; simp at hb
          replace hb:= setSubsetIff.mp hb _ ht; simp at hb
          refine' Exists.elim hb _
          intro nb hnb; rw [hnb.right.symm]
          exact nb.property.left
        exact ⟨_,h1.right,p5,p7 ⟩ 
      exact ⟨mp,mpr ⟩ 
    calc 
      nhds a = ⟨(nhds a).sets,_,_,_ ⟩ := rfl
      _ = ⟨(Filter.generate s).sets,_,_,_ ⟩ := by simp_rw [p3]
  exact ⟨p1⟩ 

def FirstCountableTopologyTofstCountable [TopologicalSpace α] 
(inst:TopologicalSpace.FirstCountableTopology α ):fstCountable α := by          
  have p1:(∀ (x : α), ∃ nbB:neighbBasis x, atMostCountable nbB.neighbs) := by
    intro x
    let p2:=inst.nhds_generated_countable x
    simp [Filter.IsCountablyGenerated] at p2
    refine' Exists.elim p2.out _
    intro b hb
    by_cases c:b.Nonempty 
    case neg =>
      replace c:=setNotNonemptyIff.mp c
      rw [c] at hb; 
      let nbB:neighbBasis x := {
        neighbs := {⟨univ,by simp, univIsOpen ⟩ }
        exists_contained := by
          intro nbx
          let p3:=mem_nhds_iff.mpr 
            ⟨nbx.set,(subset_rfl:nbx.set ⊆ nbx.set),nbx.property.right, nbx.property.left ⟩ 
          rw [hb.right,Filter.generate_empty] at p3; simp at p3
          exact ⟨⟨univ,by simp, univIsOpen ⟩,by simp, by rw [p3] ⟩ }
      have p3:nbB.neighbs.atMostCountable := by
        simp only [atMostCountable]
        refine' ⟨fun _ =>⟨univ,by simp, univIsOpen ⟩,by simp ⟩ 
      exact ⟨_,p3 ⟩ 
    case pos =>
      have p3:b.atMostCountable := by
        refine' Exists.elim (Set.countable_iff_exists_subset_range.mp hb.left) _
        intro f hf
        have p4:b⊆Im(f,univ) := by
          simp; exact hf
        exact subsetOfCountable c p4 (imageOfCountable f NIsCountable)
      refine' Exists.elim p3 _
      intro f hf
      have p5:∀ {s:Set α}, s∈Im(f,univ) -> s∈ nhds x := by
        intro s hs; rw [hb.right]; rw [hf.symm] at hs
        refine' Filter.mem_generate_iff.mpr _
        have p6: {s}⊆  b := by simp; exact hs
        exact ⟨_,p6,by simp,by simp; exact subset_rfl ⟩ 
      let f':= fun n:Nat =>
        (⟨ _, (choose_spec (mem_nhds_iff.mp (p5 (by simp:f n∈Im(f,univ))))).right.right,
        (choose_spec (mem_nhds_iff.mp (p5 (by simp:f n∈Im(f,univ))))).right.left⟩ :neighb x)
      have p6:∀(n:Nat), (f' n).set  ⊆ f n := by
        intro n 
        exact (choose_spec (mem_nhds_iff.mp (p5 (by simp:f n∈Im(f,univ))))).left
      let g1:= fun n:Nat => Im(fun k=>(f' k).set, (Finset.range (n+1))).toFinset
      let g2:= fun n:Nat => ⋂₀ (g1 n).toSet
      have p7 n : ∀ {s:Set α}, s∈ g1 n -> IsOpen s := by
        intro s hs; simp at hs
        refine' Exists.elim hs _
        intro n' hn'; rw [hn'.right.symm]
        exact (choose_spec (mem_nhds_iff.mp (p5 (by simp:f n'∈Im(f,univ))))).right.left
      replace p7 :=  fun n => finsetOpenInter (p7 n)
      have p8:∀ (n : ℕ), x∈ g2 n := by
        intro n; simp
        intro n' _
        exact (choose_spec (mem_nhds_iff.mp (p5 (by simp:f n'∈Im(f,univ))))).right.right
      let g:ℕ->neighb x := fun n => ⟨_,p8 n,p7 n ⟩ 
      have p9 {k1 k2:Nat}: k1≤k2 -> (g k2).set ⊆ f k1 := by
        intro h1
        have p10:(g k2).set ⊆ (g k1).set := by
          refine' setSubsetIff.mpr _
          intro z hz; simp at hz; simp
          intro i hi
          have p11:i <  k2 + 1 := calc
            _ < _ :=hi   
            _ ≤ _ :=by simp ;exact h1
          exact hz _ p11
        have p11:(g k1).set⊆ (f' k1).set := by
          refine' setSubsetIff.mpr _
          intro z hz; simp at hz; simp
          exact hz k1 (by simp)
        calc 
          _ ⊆ _ := p10
          _ ⊆ _ := p11
          _ ⊆ _ := p6 k1
      let nbB:neighbBasis x := {
        neighbs :=Im(g,univ)
        exists_contained := by
          intro nb 
          let p10:=mem_nhds_iff.mpr ⟨nb.set,subset_rfl,nb.property.right,nb.property.left ⟩ 
          rw [hb.right] at p10; replace p10:=Filter.mem_generate_iff.mp p10
          refine' Exists.elim p10 _
          intro l p10
          refine' Exists.elim p10 _
          intro hl p10
          by_cases c2:l.Nonempty
          case neg =>
            replace c2:=setNotNonemptyIff.mp c2; 
            rw [c2] at p10; simp at p10
            replace p10:=subset_antisymm p10 (by simp)
            rw [p10.symm]; exact ⟨g 1, by simp,by simp ⟩ 
          case pos =>  
            let sN:=Im(Function.invFun f,l)
            have p11:sN.Finite := Finite.image _ p10.left
            have p12:p11.toFinset.toSet = sN := by simp
            let natToReal :Nat ->Real := fun x => x
            have p13:(p11.toFinset.toList.map natToReal) ≠ [] := by
              by_contra hc
              replace hc:=congrArg List.length hc; simp at hc
              exact (setNonemptyIff.mp c2) hc
            refine' Exists.elim (SUP_INF.maxIsReachable p13) _
            intro k p13
            refine' Exists.elim p13 _
            intro p14 p13
            have p15:k < p11.toFinset.toList.length := by
              let p14':=p14; rw [List.length_map] at p14'
              exact p14'
            let N:=  (Finset.toList (Finite.toFinset p11))[k]
            have p16:∀nn:Nat, nn∈p11.toFinset -> nn≤ N := by
              intro nn hnn
              have p17:natToReal nn ∈ (p11.toFinset.toList.map natToReal) := by
                simp only [List.mem_map]; refine' ⟨nn,Finset.mem_toList.mpr hnn,rfl ⟩ 
              replace p17:=SUP_INF.maxIsGreatest p17
              rw [p13.symm,EReal.coe_le_coe_iff,listMapNEqFN] at p17; 
              simp at p17; exact p17
            refine' ⟨g N,by simp,subset_trans (setSubsetIff.mpr _) p10.right ⟩ 
            intro z hz;  simp
            intro t ht
            have p17: (f ∘ (Function.invFun f)) t = t := by
              let p18:= hf ▸ (setSubsetIff.mp hl _ ht); 
              rw [mem_image] at p18
              refine' Exists.elim p18 _
              intro nn hnn
              exact Function.invFun_eq ⟨_,hnn.right⟩ 
            have p18:(Function.invFun f) t∈ sN :=by 
              simp only [mem_image]
              exact ⟨_,ht,rfl⟩ 
            rw [p12.symm] at p18; rw [p17.symm]
            exact setSubsetIff.mp (p9 (p16 _ p18)) _ hz   }
      exact ⟨nbB,⟨g,rfl⟩⟩ 
  exact ⟨p1⟩ 

def sndCountableToSecondCountableTopology  [ts:TopologicalSpace α] (snd:sndCountable α):
TopologicalSpace.SecondCountableTopology α  := by
  have p1:(∃ b, Set.Countable b ∧ ts = TopologicalSpace.generateFrom b) := by
    refine' Exists.elim snd.property _
    intro tB htB
    have p2:tB.sets.Countable := by
      refine' Exists.elim htB _
      intro f hf; rw [hf]; simp
      exact countable_range f
    refine' ⟨_,p2,TopologicalSpaceEqIff.mpr _⟩ 
    intro s
    have mp:ts.IsOpen s -> (TopologicalSpace.generateFrom tB.sets).IsOpen s := by
      intro h; simp [TopologicalSpace.generateFrom]
      refine' Exists.elim (tB.any_open_is_sunion h) _
      intro b hb; rw [hb.right]
      have p2: (∀ (t : Set α), t ∈ b → TopologicalSpace.GenerateOpen tB.sets t) := by
        intro t ht
        replace ht:=setSubsetIff.mp hb.left _ ht
        exact .basic _ ht
      exact .sUnion _ p2
    have mpr: (TopologicalSpace.generateFrom tB.sets).IsOpen s -> ts.IsOpen s := by
      intro h ; simp [TopologicalSpace.generateFrom] at h
      let rec p3: ∀{t:Set α}, TopologicalSpace.GenerateOpen tB.sets t -> ts.IsOpen t := by
        intro t ht
        match ht with
        |.basic t' ht' =>
          exact tB.sets_forall_open ht'
        |.univ =>
          exact univIsOpen
        |.inter t1' t2' ht1' ht2' =>
          exact openInter (p3 ht1') (p3 ht2')
        |.sUnion b hb =>
          replace hb: ∀ {s : Set α}, s ∈ b -> ts.IsOpen s:=
            fun  ht' => p3 (hb _ ht')
          exact openSUnion hb
      exact p3 h
    exact ⟨mp,mpr⟩ 
  exact ⟨p1⟩ 

/-
The definition of second countability in mathlib might be weaker than that defined here. 
-/

lemma tendstoConvergesTo [TopologicalSpace α] {x:sequenceN α} {x0:α}:
Filter.Tendsto x Filter.atTop (nhds x0) ↔ x.convergesTo x0 := by 
  have mp: Filter.Tendsto x Filter.atTop (nhds x0) -> x.convergesTo x0 := by
    intro h1; simp
    intro u   ; simp only [Filter.Tendsto] at h1
    have p1:u.set ∈ nhds x0 := by 
      refine' mem_nhds_iff.mpr ⟨ _,subset_rfl,u.property.right,u.property.left⟩ 
    replace p2:= Filter.mem_map.mp
      (Filter.le_def.mp h1 _ p1)
    simp at p2
    refine' Exists.elim p2 _
    intro N hN
    refine' ⟨N,_ ⟩ 
    intro n hn; exact hN _ hn
  have mpr: x.convergesTo x0 ->  Filter.Tendsto x Filter.atTop (nhds x0) := by
    intro h1; simp [Filter.Tendsto]
    refine' Filter.le_def.mpr _
    intro t ht; replace ht:=mem_nhds_iff.mp ht
    refine' Exists.elim ht _
    intro t' ht'
    refine' Filter.mem_map.mpr _
    simp only [sequenceN.convergesTo] at h1
    refine' Exists.elim (h1 ⟨_, ht'.right.right,ht'.right.left ⟩ ) _
    intro N hN 
    have p1:{k:ℕ | N≤ k } ⊆ PreIm(x,t) := by
      intro k hk;
      exact setSubsetIff.mp ht'.left _  (hN hk)
    exact Filter.mem_of_superset (Filter.mem_atTop _) p1
  exact ⟨mp,mpr⟩ 

end CoeMathlib

namespace  PointSetTopology

/-

TODO: First or second countability of either space in a pair of homeomorphic spaces implies the first or second countability of the other.

-/



end PointSetTopology











