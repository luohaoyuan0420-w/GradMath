import GradMath.Topology.PointSet.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph
import GradMath.Basic.SUP_INF
import Mathlib.Topology.Maps
import Mathlib.Topology.Bases

noncomputable section

namespace PointSetTopology

open FUNCTION SET Set LIST FINSET Classical NAT COUNTABLE 

universe u_1 u_2 u_3
variable {α: Type u_1} {β :Type u_2}

lemma subspaceDef {s:Set α} [inst:TopologicalSpace α] {t:Set (Subtype s)}: 
IsOpen t ↔ ∃(t':Set α),IsOpen t'∧ PreIm(Subtype.val,t') = t:= by  
  have mp:IsOpen t ->∃(t':Set α),IsOpen t'∧ PreIm(Subtype.val,t') = t  := by
    intro h1; 
    rw [IsOpen,TopologicalSpace.IsOpen,instTopologicalSpaceSubtype,
      TopologicalSpace.induced] at h1; simp at h1
    exact h1
  have mpr: (∃(t':Set α),IsOpen t'∧ PreIm(Subtype.val,t')=t) ->IsOpen t:= by
    intro h1;
    rw  [IsOpen,TopologicalSpace.IsOpen,instTopologicalSpaceSubtype,
      TopologicalSpace.induced]; simp
    exact h1
  exact ⟨mp,mpr⟩ 

lemma subspaceDef' {s:Set α} [inst:TopologicalSpace α] {t:Set (Subtype s)}:
IsClosed t ↔ ∃(t':Set α),IsClosed t'∧PreIm(Subtype.val,t')=t := by
  have mp:IsClosed t -> ∃(t':Set α),IsClosed t'∧PreIm(Subtype.val,t')=t := by
    intro h1; 
    refine' Exists.elim (subspaceDef.mp (closedComplIsOpen h1)) _
    intro t' ht'
    let p1:= ht'.right ▸  @preImCompl (Subtype s) _ t' Subtype.val 
    rw [setComplCompl] at p1
    exact ⟨_,openComplIsClosed ht'.left,p1⟩ 
  have mpr: (∃(t':Set α),IsClosed t'∧PreIm(Subtype.val,t')=t) -> IsClosed t := by
    intro h1
    have p1: ∃(t'':Set α),IsOpen t''∧PreIm(Subtype.val,t'')=tᶜ := by
      refine' Exists.elim  h1 _
      intro t' ht'
      refine' ⟨_,closedComplIsOpen ht'.left,_⟩ 
      rw [@preImCompl (Subtype s) _ t' Subtype.val]
      rw [ht'.right]; 
    replace p1:= openComplIsClosed (subspaceDef.mpr p1)
    rw [setComplCompl] at p1; exact p1
  exact ⟨mp,mpr⟩ 

lemma openSubsetOfOpenSubset {S : Set α }{U:Set (Subtype S)} [TopologicalSpace α] 
(h1:IsOpen U)(h2:IsOpen S): IsOpen (Im(Subtype.val,U)) := by
  refine' Exists.elim (subspaceDef.mp h1) _
  intro U' hU'
  have p1: (Im(Subtype.val,U)) = U' ∩ S := by
    refine' setEqIff.mpr _
    intro x
    have mp: x ∈ Im(Subtype.val,U) ->x ∈ U' ∩ S := by
      intro h1; simp ; simp at h1
      refine' Exists.elim h1 _
      intro p2 p3; rw [hU'.right.symm] at p3
      simp at p3; exact ⟨p3,p2⟩ 
    have mpr: x ∈ U' ∩ S -> x ∈ Im(Subtype.val,U) := by
      intro h1; simp; simp at h1
      rw [hU'.right.symm]; simp
      exact ⟨h1.right,h1.left⟩ 
    exact ⟨mp,mpr⟩ 
  rw [p1]; exact openInter hU'.left h2

lemma closedSubsetOfClosedSubset {S : Set α }{U:Set (Subtype S)} [TopologicalSpace α]
(h1:IsClosed U)(h2:IsClosed S): IsClosed (Im(Subtype.val,U)) := by
  refine' Exists.elim (subspaceDef'.mp h1) _
  intro U' hU'
  have p1: (Im(Subtype.val,U)) = U' ∩ S := by
    refine' setEqIff.mpr _
    intro x
    have mp: x ∈ Im(Subtype.val,U) ->x ∈ U' ∩ S := by
      intro h1; simp ; simp at h1
      refine' Exists.elim h1 _
      intro p2 p3; rw [hU'.right.symm] at p3
      simp at p3; exact ⟨p3,p2⟩ 
    have mpr: x ∈ U' ∩ S -> x ∈ Im(Subtype.val,U) := by
      intro h1; simp; simp at h1
      rw [hU'.right.symm]; simp
      exact ⟨h1.right,h1.left⟩ 
    exact ⟨mp,mpr⟩ 
  rw [p1]; exact closedInter hU'.left h2

lemma openSubsetInSubset {S:Set α}{U:Set (Subtype S)}[TopologicalSpace α]
(h:IsOpen (Im(Subtype.val,U))): IsOpen U := by 
  refine' subspaceDef.mpr ⟨Im(Subtype.val,U),h,_⟩ 
  refine' setEqIff.mpr _
  intro x; 
  have mp: x ∈ PreIm(Subtype.val,Im(Subtype.val,U)) -> x ∈ U := by
    intro h1; simp at h1; exact h1.right
  have mpr:x∈U -> x ∈ PreIm(Subtype.val,Im(Subtype.val,U)) := by
    intro h1; simp ; exact ⟨x.property,h1⟩ 
  exact ⟨mp,mpr⟩ 

lemma closedSubsetInSubset {S:Set α}{U:Set (Subtype S)}[TopologicalSpace α]
(h:IsClosed (Im(Subtype.val,U))): IsClosed U := by 
  refine' subspaceDef'.mpr ⟨Im(Subtype.val,U),h,_⟩ 
  refine' setEqIff.mpr _
  intro x; 
  have mp: x ∈ PreIm(Subtype.val,Im(Subtype.val,U)) -> x ∈ U := by
    intro h1; simp at h1; exact h1.right
  have mpr:x∈U -> x ∈ PreIm(Subtype.val,Im(Subtype.val,U)) := by
    intro h1; simp ; exact ⟨x.property,h1⟩ 
  exact ⟨mp,mpr⟩ 

lemma continuousRestrictDomain [TopologicalSpace α] [TopologicalSpace β] {f:α->β} (h:Continuous f)
{S: Set α}: Continuous (f∘Subtype.val:Subtype S ->β) := by 
  refine' continuousDef.mpr _
  intro t ht; rw [preImComp]
  refine' subspaceDef.mpr ⟨PreIm(f,t), _⟩ 
  exact ⟨continuousDef.mp h ht,(by simp) ⟩ 

lemma continuousRestrictCodomain [TopologicalSpace α][TopologicalSpace β]{f:α->β}(h1:Continuous f)
{S: Set β} (h2:Im(f,univ)⊆S):(Continuous (fun x =>⟨f x,setSubsetIff.mp h2 _ ((mem_image f univ (f x)).mpr ⟨x,mem_univ x,rfl ⟩ ) ⟩ :α->Subtype S)) := by 
  refine' continuousDef.mpr _
  intro t ht;
  refine' Exists.elim (subspaceDef.mp ht) _
  intro t' ht'
  have p1: PreIm(f,t') = PreIm((fun x =>⟨f x,setSubsetIff.mp h2 _ 
  ((mem_image f univ (f x)).mpr ⟨x,mem_univ x,rfl ⟩ ) ⟩ :α->Subtype S),t) := by
    refine' setEqIff.mpr _
    intro z ; 
    have mp:z∈PreIm(f,t') ->z∈PreIm((fun x =>⟨f x,setSubsetIff.mp h2 _ 
    ((mem_image f univ (f x)).mpr ⟨x,mem_univ x,rfl ⟩ ) ⟩ :α->Subtype S),t) := by
      intro h1;rw [ht'.right.symm]; simp; simp at h1; exact h1
    have mpr:z∈ PreIm((fun x =>⟨f x,setSubsetIff.mp h2 _ ((mem_image f univ (f x)).mpr 
    ⟨x,mem_univ x,rfl ⟩ ) ⟩ :α->Subtype S),t) -> z∈PreIm(f,t') := by
      intro h1; rw [ht'.right.symm] at h1;simp ; simp at h1; exact h1
    exact ⟨mp,mpr⟩ 
  rw [p1.symm]; exact continuousDef.mp h1 ht'.left

lemma continuousExpandCodomain [inst1:TopologicalSpace α][inst2:TopologicalSpace β]
{S: Set β}{f:α-> Subtype S}
(h1:Continuous f):Continuous (Subtype.val∘f) := by  
  let p1:= (@continuousDef α β inst1 inst2 (Subtype.val ∘ f)).mpr
  refine' p1 _ 
  intro t' ht'
  set t:=(PreIm((Subtype.val:Subtype S->β ),t')) with HH
  have p1: PreIm((Subtype.val ∘ f),t') = PreIm(f,t) := by 
    refine' setEqIff.mpr _
    intro z ; simp
  let p2:=subspaceDef.mpr ⟨_,ht',HH.symm ⟩ 
  rw [p1]; exact continuousDef.mp h1 p2

lemma uniqueSubspaceTopology [inst:TopologicalSpace α] (S:Set α) (U: Set (Subtype S)) (h:U.Nonempty): 
@Homeomorph _ _ (@instTopologicalSpaceSubtype _ U _ ) 
(@instTopologicalSpaceSubtype _ (Im(Subtype.val,U)) inst) := by
  have p1:Nonempty (Subtype U) := by
    simp [Set.Nonempty] at h
    refine' Exists.elim h _
    intro x hx
    refine' Exists.elim hx _
    intro hx1 hx2
    let x':Subtype U := ⟨_,hx2⟩ 
    exact Nonempty.intro x'
  exact {
  toEquiv:= {
    toFun:= fun x => ⟨x.val.val,(mem_image Subtype.val U _).mpr ⟨_,x.property,rfl ⟩  ⟩ 
    invFun:=  
      Function.invFun (fun x =>⟨x.val.val,(mem_image Subtype.val U _).mpr ⟨_,x.property,rfl⟩⟩)
    left_inv:=by
      refine' Function.leftInverse_invFun _
      simp [Function.Injective]
    right_inv := by
      refine' Function.rightInverse_invFun _
      simp only [Function.Surjective]
      intro a 
      refine' Exists.elim ((mem_image _ _ _).mp ( mem_def.mpr a.property )) _
      intro a2 ha2; refine' ⟨⟨a2,ha2.left ⟩ ,_ ⟩ 
      simp_rw [ha2] }
  continuous_toFun:= by
    simp; refine' continuousDef.mpr _
    intro v hv; refine' subspaceDef.mpr _
    refine' Exists.elim ( subspaceDef.mp hv) _
    intro t' ht'; 
    let p3:=continuousDef.mp (@continuous_subtype_val α _ S) ht'.left
    refine' ⟨PreIm((Subtype.val:Subtype S->α) ,t') ,p3,_ ⟩ 
    refine' setEqIff.mpr _
    intro z; simp
    have mp: ↑↑z ∈ t' ->⟨↑↑z,(mem_image Subtype.val U _).mpr ⟨_,z.property,rfl⟩⟩ ∈ v := by
      intro h1; rw [ht'.right.symm]; simp; exact h1
    have mpr: ⟨↑↑z,(mem_image Subtype.val U _).mpr ⟨_,z.property,rfl⟩⟩∈v -> ↑↑z ∈ t':= by
      intro h1; rw [ht'.right.symm] at h1; simp at h1; exact h1
    exact ⟨mp,mpr⟩ 
  continuous_invFun:= by
    simp; refine' continuousDef.mpr _
    intro v hv;  
    refine' Exists.elim (subspaceDef.mp hv) _
    intro v' hv'
    refine' Exists.elim (subspaceDef.mp hv'.left) _
    intro v'' hv''
    refine' subspaceDef.mpr ⟨_,hv''.left,_ ⟩ 
    refine' setEqIff.mpr _
    intro z;
    refine' Exists.elim  ((mem_image _ _ _).mp (mem_def.mpr z.property)) _
    intro z' hz' 
    have p2:(fun x =>⟨x.val.val,(mem_image Subtype.val U _).mpr ⟨_,x.property,rfl⟩⟩)
      (⟨z',hz'.left ⟩:Subtype U)  = z := by 
      simp; simp_rw [hz'.right]
    replace p2:=congrArg (Function.invFun (fun (x:Subtype U) =>
      ⟨x.val.val,(mem_image Subtype.val U _).mpr ⟨_,x.property,rfl⟩⟩)) p2
    have p3: Function.Injective  ((fun x => ⟨x.val.val,(mem_image Subtype.val U _).mpr
      ⟨_,x.property,rfl⟩⟩): Subtype U ->Subtype (Im(Subtype.val,U))) := by 
        simp  [Function.Injective]
    replace p3:= congrFun (funcLeftInvInjComp p3) ⟨z',hz'.left ⟩
    simp at p3 p2; rw [p3] at p2;
    have mp: z∈PreIm(Subtype.val,v'') ->
    z ∈ PreIm(Function.invFun (fun x =>⟨x.val.val,(mem_image Subtype.val U _).mpr 
    ⟨_,x.property,rfl⟩⟩),v) := by
      intro h1; 
      simp; 
      rw [p2.symm,hv'.right.symm,hv''.right.symm] 
      simp; rw [hz'.right] ;  simp at h1; exact h1
    have mpr: z ∈ PreIm(Function.invFun (fun x =>⟨x.val.val,(mem_image Subtype.val U _).mpr 
    ⟨_,x.property,rfl⟩⟩),v) -> z∈PreIm(Subtype.val,v'') := by
      intro h1; rw [hv'.right.symm,hv''.right.symm] at h1; simp at h1
      rw [p2.symm] at h1; simp at h1; simp
      rw [hz'.right.symm] ;exact h1
    exact ⟨mp,mpr⟩ }

def subspaceBasisFromBasis [ts:TopologicalSpace α](tB:topologicalBasis ts)(S:Set α)
:topologicalBasis (@instTopologicalSpaceSubtype _ S _) := {
  sets:=Im(preimage Subtype.val,tB.sets)
  sets_forall_open:=by
    intro t ht; simp at ht
    refine' Exists.elim ht _
    intro t' ht'
    exact subspaceDef.mpr ⟨t',tB.sets_forall_open ht'.left,ht'.right ⟩ 
  any_open_is_sunion:=by
    intro t ht
    refine' Exists.elim (subspaceDef.mp ht) _
    intro t' ht'
    refine' Exists.elim (tB.any_open_is_sunion ht'.left) _
    intro b' hb'
    let b:Set (Set (Subtype S)):= Im(preimage Subtype.val,b')
    have p1:b ⊆ Im(preimage Subtype.val,tB.sets) := by
      refine' setSubsetIff.mpr _
      intro s hs; simp; simp at hs
      refine' Exists.elim hs _
      intro s' hs'
      exact ⟨_,setSubsetIff.mp hb'.left _ hs'.left,hs'.right⟩ 
    have p2: t = ⋃₀ b := by
      refine' setEqIff.mpr _
      intro x ; 
      have mp: x ∈ t -> x ∈ ⋃₀ b := by
        intro h1; 
        rw [ht'.right.symm,mem_preimage,hb'.right,mem_sUnion] at h1
        rw [mem_sUnion]; 
        refine' Exists.elim h1 _
        intro r hr; 
        simp; exact ⟨_,hr⟩ 
      have mpr: x∈⋃₀ b -> x∈t := by
        intro h1 
        rw [ht'.right.symm,mem_preimage,hb'.right,mem_sUnion]
        rw [mem_sUnion] at h1
        simp at h1; exact h1
      exact ⟨mp,mpr⟩ 
    exact ⟨_,p1,p2⟩ }
  
lemma subtypeValIsContinuous [TopologicalSpace α] {S:Set α}:
Continuous (Subtype.val:(Subtype S)->α):=continuous_subtype_val

lemma subtypeValIsEmbedding [TopologicalSpace α] {S:Set α}:
Embedding (Subtype.val:(Subtype S)->α) := embedding_subtype_val     

lemma convergesInSubspaceIff [TopologicalSpace α]{S:Set α}{x:(Subtype S)}{a:sequenceN (Subtype S)} :
a.convergesTo x ↔ sequenceN.convergesTo (Subtype.val∘a) x.val := by 
  have mp: a.convergesTo x -> sequenceN.convergesTo (Subtype.val∘a) x.val := by
    intro h1; simp only [sequenceN.convergesTo] at h1
    simp only [sequenceN.convergesTo]
    intro nb'
    set nbset:Set (Subtype S):=PreIm(Subtype.val,nb'.set) with HH
    have p1:x∈PreIm(Subtype.val,nb'.set) := by
      exact nb'.property.left
    let nb:neighb x:= ⟨nbset,p1,subspaceDef.mpr ⟨_,nb'.property.right,HH.symm ⟩ ⟩ 
    refine' Exists.elim (h1 nb) _
    intro N hN
    refine' ⟨N,_⟩ 
    intro n hn
    replace hN:=hN hn
    simp at hN; exact hN
  have mpr: (sequenceN.convergesTo (Subtype.val∘a) x.val) -> a.convergesTo x := by
    intro h1; simp only [sequenceN.convergesTo] at h1
    simp only [sequenceN.convergesTo]
    intro nb
    refine' Exists.elim (subspaceDef.mpr nb.property.right ) _
    intro nbset' hnbset'
    have p1:x.val ∈ nbset' := by 
      let p2:=hnbset'.right.symm ▸ nb.property.left
      exact p2
    let nb':neighb x.val := ⟨nbset',p1,hnbset'.left⟩ 
    refine' Exists.elim (h1 nb') _
    intro N hN
    refine' ⟨N,_⟩
    intro n hn
    replace hN:=hN hn
    rw [hnbset'.right.symm]; simp
    exact hN
  exact ⟨mp,mpr⟩ 
    
@[reducible]
instance subspaceHausdorffIfHausdorff [TopologicalSpace α] [hs:HausdorffSpace α] {S:Set α}:
HausdorffSpace (Subtype S) := by 
  have p1:(∀ {x y:Subtype S},x≠y→∃(u1:neighb x)(u2:neighb y), u1.set ∩ u2.set = ∅) := by
    intro x y hxy
    have p2:x.val≠y.val := by
      by_contra hc
      have p3: x=y := calc
        x = ⟨x.val,_⟩  := rfl
        _ = ⟨y.val,_⟩ := by simp_rw [hc]
      exact hxy p3
    replace p2:=hs.property p2
    refine' Exists.elim p2 _
    intro v1 p2
    refine' Exists.elim p2 _
    intro v2 p2
    let u1:neighb x:= ⟨PreIm(Subtype.val,v1.set),v1.property.left,
      continuousDef.mp (subtypeValIsContinuous:Continuous ((Subtype.val:Subtype S -> α)))
        v1.property.right⟩ 
    let u2:neighb y:=⟨PreIm(Subtype.val,v2.set),v2.property.left,
      continuousDef.mp (subtypeValIsContinuous:Continuous ((Subtype.val:Subtype S -> α)))
        v2.property.right⟩ 
    refine' ⟨u1,u2,_⟩ ; simp
    by_contra hc
    refine' Exists.elim (setNonemptyIff.mpr hc) _
    intro a ha
    simp at ha
    have p3: a.val∈ v1.set ∩ v2.set := ha
    exact (setNonemptyIff.mp ⟨_,p3⟩)  p2
  exact ⟨p1⟩ 

@[reducible]
lemma subspaceFstCountableIfFstCountable [TopologicalSpace α] [fst:fstCountable α] {S:Set α}:
fstCountable (Subtype S)  := by 
  have p1:∀ (x : Subtype S), ∃ nbB:neighbBasis x, atMostCountable nbB.neighbs := by
    intro x
    let f:neighb x.val->neighb x:= fun neig =>
      ⟨PreIm((Subtype.val:Subtype S -> α),neig.set),mem_preimage.mpr neig.property.left,
      continuousDef.mp subtypeValIsContinuous neig.property.right ⟩
    refine' Exists.elim (fst.property x) _
    intro nbB' hnbB'
    let nbB:neighbBasis x := {
      neighbs:=Im(f,nbB'.neighbs)
      exists_contained := by
        intro nb_given
        refine' Exists.elim (subspaceDef.mp nb_given.property.right) _
        intro t' ht'
        have p2:x.val ∈ t' := by
          let p3:=ht'.right.symm ▸ nb_given.property.left
          exact p3
        refine' Exists.elim (nbB'.exists_contained ⟨_,p2,ht'.left⟩ ) _
        intro nb'_found hnb'_found; simp at hnb'_found
        simp; refine' ⟨_,hnb'_found.left,_ ⟩ 
        refine' setSubsetIff.mpr _
        intro a ha; exact ht'.right ▸ ( setSubsetIff.mp 
          (preImSubset (Subtype.val:(Subtype S)->α) hnb'_found.right) _ ha)}
    exact ⟨nbB,imageOfCountable f hnbB'⟩ 
  exact ⟨p1⟩ 

@[reducible]
instance subspaceSndCountableIfSndCountable [ts:TopologicalSpace α] [snd:sndCountable α] {S:Set α}:
sndCountable (Subtype S)  := by 
  have p1:(∃ tb:topologicalBasis (@instTopologicalSpaceSubtype _ S _), atMostCountable tb.sets) := by
    refine' Exists.elim snd.property _
    intro tB' htB'
    let f:= preimage (Subtype.val:Subtype S -> α)
    let tB:topologicalBasis (@instTopologicalSpaceSubtype _ S _) :={
      sets:=Im(f,tB'.sets)
      sets_forall_open := by
        intro t ht; simp only [mem_image] at ht 
        refine' Exists.elim ht _
        intro s hs; rw [hs.right.symm]
        exact continuousDef.mp (subtypeValIsContinuous:Continuous 
          (Subtype.val:Subtype S ->α)) (tB'.sets_forall_open hs.left)
      any_open_is_sunion:= by
        intro s_given hs_given
        refine' Exists.elim (subspaceDef.mp hs_given) _
        intro s'_given hs'_given
        refine' Exists.elim (tB'.any_open_is_sunion hs'_given.left) _
        intro b hb; refine' ⟨Im(f,b),imSubset _ hb.left ,_⟩ 
        refine' setEqIff.mpr _
        intro a
        have mp:a ∈ s_given -> a ∈ ⋃₀ Im(f,b) := by
          intro h1; simp only [mem_sUnion]
          rw [hs'_given.right.symm,hb.right] at h1
          simp only [mem_preimage,mem_sUnion] at h1
          refine' Exists.elim h1 _
          intro t' ht'
          refine' ⟨f t',by simp [mem_image];exact ⟨_,ht'.left,by simp⟩ ,_⟩ 
          simp; exact ht'.right
        have mpr: a ∈ ⋃₀ Im(f,b)->a ∈ s_given := by
          intro h1; simp only [mem_sUnion] at h1
          rw [hs'_given.right.symm,hb.right] 
          simp only [mem_preimage,mem_sUnion]
          refine' Exists.elim h1 _
          intro t _; simp [mem_image] at h1
          exact h1
        exact ⟨mp,mpr⟩  }
    exact ⟨tB,imageOfCountable f htB' ⟩ 
  exact ⟨p1⟩ 
          
lemma continuousGluing [TopologicalSpace α][TopologicalSpace β](A:openCover (univ:Set α))
(F:(si:Subtype (A.sets))->(Subtype si.val)->β) (H1:∀(si:Subtype (A.sets)), Continuous (F si))
(H2:∀(si sj:Subtype (A.sets))(x:α),(h:x∈ si.val ∩ sj.val)-> 
F si ⟨x,((mem_inter_iff _ _ _).mp h).left⟩  = F sj ⟨x,((mem_inter_iff _ _ _).mp h).right⟩  ):
∃! f:α->β, Continuous f ∧ (∀(si:Subtype (A.sets)), F si = f∘Subtype.val) := by 
  simp only [ExistsUnique]
  let f:= fun (x:α) => 
    F ⟨_,(choose_spec (mem_sUnion.mp (A.is_covered  (mem_univ _:x∈univ)))).left⟩  
      ⟨_,(choose_spec (mem_sUnion.mp (A.is_covered  (mem_univ _:x∈univ)))).right ⟩ 
  refine' ⟨f,_⟩ 
  have p1:Continuous f := by
    refine' continuousDef.mpr _
    intro t ht
    have p2: PreIm(f,t) = ⋃₀ Im(fun s=>Im(Subtype.val ,PreIm(F s,t)),(univ:Set (Subtype A.sets))) := by
      refine' setEqIff.mpr _
      intro x
      let si:Subtype A.sets:=⟨_,(choose_spec (mem_sUnion.mp (A.is_covered  (mem_univ _:x∈univ)))).left⟩
      have p3:Im(Subtype.val,PreIm(F si,t))∈Im(fun s => Im(Subtype.val,PreIm(F s,t)),univ) := by
        refine' (mem_image _ _ _).mpr ⟨si,_ ⟩ 
        simp
      have mp: x∈PreIm(f,t) -> 
        x∈ ⋃₀ Im(fun s=>Im(Subtype.val ,PreIm(F s,t)),(univ:Set (Subtype A.sets))) := by
        intro h1; 
        refine' mem_sUnion.mpr _
        have p4:x∈Im(Subtype.val,PreIm(F si,t)) := by
          refine' (mem_image _ _ _).mpr 
            ⟨⟨_,(choose_spec (mem_sUnion.mp (A.is_covered  (mem_univ _:x∈univ)))).right ⟩ ,h1,rfl⟩ 
        exact ⟨_,p3,p4⟩ 
      have mpr: x∈ ⋃₀ Im(fun s=>Im(Subtype.val ,PreIm(F s,t)),(univ:Set (Subtype A.sets)))
      ->x∈PreIm(f,t) := by
        intro h1
        replace h1:=mem_sUnion.mp h1
        refine' Exists.elim h1 _
        intro s hs;
        let hsl:=hs.left; simp only [mem_image] at hsl
        refine' Exists.elim hsl _
        intro s' hs'
        let hsr:=hs'.right.symm ▸ hs.right
        simp only [mem_image] at hsr
        refine' Exists.elim hsr _
        intro x' hx'
        have p4:∃ t, (t ∈ A.sets ∧ x ∈ t) := ⟨_,s'.property,hx'.right▸ x'.property ⟩ 
        simp at hx'; simp
        rw[← H2 s' ⟨_,(choose_spec p4).left⟩ x (mem_inter (hx'.right▸ x'.property) 
          (choose_spec p4).right)]
        simp_rw [hx'.right.symm]
        exact hx'.left
      exact ⟨mp,mpr⟩ 
    have p3:∀{x : Set α},x∈Im(fun s => Im(Subtype.val,PreIm(F s,t)),univ)→ IsOpen x := by
      intro x hx; simp only [mem_image] at hx
      refine' Exists.elim hx _
      intro x' hx'; rw [hx'.right.symm]
      refine' openSubsetOfOpenSubset (continuousDef.mp (H1 x') ht) (A.sets_forall_open x'.property)
    rw [p2]; exact openSUnion p3
  have p2: ∀ (si : Subtype A.sets), F si = f ∘ Subtype.val := by
    intro si; refine' funcEqIff.mpr _
    intro a; 
    let p3:=H2 si 
      ⟨_,(choose_spec (mem_sUnion.mp (A.is_covered  (mem_univ _:a.val∈univ)))).left⟩  
      a.val (mem_inter a.property
        (choose_spec (mem_sUnion.mp (A.is_covered  (mem_univ _:a.val∈univ)))).right)
    simp; rw [p3.symm]; 
  refine' ⟨⟨p1,p2 ⟩,_  ⟩ 
  intro f' hf'; refine' funcEqIff.mpr _
  intro a; 
  let p3:=hf'.right ⟨_,(choose_spec (mem_sUnion.mp (A.is_covered  
    (mem_univ _:a∈univ)))).left⟩
  exact (congrFun p3 ⟨_,(choose_spec (mem_sUnion.mp 
    (A.is_covered  (mem_univ _:a∈univ)))).right⟩ ).symm

lemma continuousGluing' [TopologicalSpace α][TopologicalSpace β](A:closedCover (univ:Set α)) 
(inst:A.sets.Finite)(F:(si:Subtype (A.sets))->(Subtype si.val)->β) 
(H1:∀(si:Subtype (A.sets)), Continuous (F si))
(H2:∀(si sj:Subtype (A.sets))(x:α),(h:x∈ si.val ∩ sj.val)-> 
F si ⟨x,((mem_inter_iff _ _ _).mp h).left⟩  = F sj ⟨x,((mem_inter_iff _ _ _).mp h).right⟩  ):
∃! f:α->β, Continuous f ∧ (∀(si:Subtype (A.sets)), F si = f∘Subtype.val) := by 
  simp only [ExistsUnique]
  let f:= fun (x:α) => 
    F ⟨_,(choose_spec (mem_sUnion.mp (A.is_covered  (mem_univ _:x∈univ)))).left⟩  
      ⟨_,(choose_spec (mem_sUnion.mp (A.is_covered  (mem_univ _:x∈univ)))).right ⟩ 
  refine' ⟨f,_⟩ 
  have p1:Continuous f := by
    refine' continuousDef'.mpr _
    intro t ht
    have p2: PreIm(f,t) = ⋃₀ Im(fun s=>Im(Subtype.val ,PreIm(F s,t)),(univ:Set (Subtype A.sets))) := by
      refine' setEqIff.mpr _
      intro x
      let si:Subtype A.sets:=⟨_,(choose_spec (mem_sUnion.mp (A.is_covered  (mem_univ _:x∈univ)))).left⟩
      have p3:Im(Subtype.val,PreIm(F si,t))∈Im(fun s => Im(Subtype.val,PreIm(F s,t)),univ) := by
        refine' (mem_image _ _ _).mpr ⟨si,_ ⟩ 
        simp
      have mp: x∈PreIm(f,t) -> 
        x∈ ⋃₀ Im(fun s=>Im(Subtype.val ,PreIm(F s,t)),(univ:Set (Subtype A.sets))) := by
        intro h1; 
        refine' mem_sUnion.mpr _
        have p4:x∈Im(Subtype.val,PreIm(F si,t)) := by
          refine' (mem_image _ _ _).mpr 
            ⟨⟨_,(choose_spec (mem_sUnion.mp (A.is_covered  (mem_univ _:x∈univ)))).right ⟩ ,h1,rfl⟩ 
        exact ⟨_,p3,p4⟩ 
      have mpr: x∈ ⋃₀ Im(fun s=>Im(Subtype.val ,PreIm(F s,t)),(univ:Set (Subtype A.sets)))
      ->x∈PreIm(f,t) := by
        intro h1
        replace h1:=mem_sUnion.mp h1
        refine' Exists.elim h1 _
        intro s hs;
        let hsl:=hs.left; simp only [mem_image] at hsl
        refine' Exists.elim hsl _
        intro s' hs'
        let hsr:=hs'.right.symm ▸ hs.right
        simp only [mem_image] at hsr
        refine' Exists.elim hsr _
        intro x' hx'
        have p4:∃ t, (t ∈ A.sets ∧ x ∈ t) := ⟨_,s'.property,hx'.right▸ x'.property ⟩ 
        simp at hx'; simp
        rw[← H2 s' ⟨_,(choose_spec p4).left⟩ x (mem_inter (hx'.right▸ x'.property) 
          (choose_spec p4).right)]
        simp_rw [hx'.right.symm]
        exact hx'.left
      exact ⟨mp,mpr⟩ 
    have p3:∀{x : Set α},x∈Im(fun s => Im(Subtype.val,PreIm(F s,t)),univ)→ IsClosed x := by
      intro x hx; simp only [mem_image] at hx
      refine' Exists.elim hx _
      intro x' hx'; rw [hx'.right.symm]
      refine' closedSubsetOfClosedSubset (continuousDef'.mp (H1 x') ht) (A.sets_forall_closed x'.property)
    have  inst2:Finite (Subtype A.sets) := Fintype.finite (Finite.fintype inst)
    have inst3: Im(fun s => Im(Subtype.val,PreIm(F s,t)),univ).Finite := 
      Finite.image _ (@finite_univ _ inst2)
    let fs:=inst3.toFinset
    have p4:fs.toSet = Im(fun s => Im(Subtype.val,PreIm(F s,t)),univ) := by simp
    rw [p4.symm] at p2
    have p5:  ∀{si : Set α},si∈fs → IsClosed si := by
      intro si hsi; 
      have p6:si∈ Im(fun s => Im(Subtype.val,PreIm(F s,t)),univ) := by
        simp; simp at hsi; exact hsi
      exact p3 p6
    rw [p2]; exact finsetClosedUnion p5
  have p2: ∀ (si : Subtype A.sets), F si = f ∘ Subtype.val := by
    intro si; refine' funcEqIff.mpr _
    intro a; 
    let p3:=H2 si 
      ⟨_,(choose_spec (mem_sUnion.mp (A.is_covered  (mem_univ _:a.val∈univ)))).left⟩  
      a.val (mem_inter a.property
        (choose_spec (mem_sUnion.mp (A.is_covered  (mem_univ _:a.val∈univ)))).right)
    simp; rw [p3.symm]; 
  refine' ⟨⟨p1,p2 ⟩,_  ⟩ 
  intro f' hf'; refine' funcEqIff.mpr _
  intro a; 
  let p3:=hf'.right ⟨_,(choose_spec (mem_sUnion.mp (A.is_covered  
    (mem_univ _:a∈univ)))).left⟩
  exact (congrFun p3 ⟨_,(choose_spec (mem_sUnion.mp 
    (A.is_covered  (mem_univ _:a∈univ)))).right⟩ ).symm

open  FinProd

lemma finProdTopologicalSpace.aux {N:ℕ}{η:Fin N → Type u_1}
(tsη:(n:Fin N)->TopologicalSpace (η n )):
∃! (ts:TopologicalSpace (∀n,η n )),∃ (tb:topologicalBasis ts), 
 {s|∃sets: (n:Fin N) ->Set (η n),s=setFinProd sets ∧ ∀m:Fin N, (tsη m).IsOpen (sets m) } =tb.sets   :=  by
  let B:Set (Set (∀n,η n)):=
    {s|∃sets: (n:Fin N) ->Set (η n),s=setFinProd sets ∧ ∀m:Fin N, (tsη m).IsOpen (sets m) }
  have p1:⋃₀ B = univ := by
    refine' setEqMpr (by simp) (setSubsetIff.mpr _)
    intro x _
    let sets:(n:Fin N) ->Set (η n):=fun n => univ
    have p2:setFinProd sets ∈ B := by
      refine' ⟨sets,by simp,fun n=>univIsOpen ⟩ ; 
    have p3:x∈setFinProd sets:= by simp
    exact mem_sUnion.mpr ⟨_,p2,p3 ⟩ 
  have p2: ∀ {s1 s2:Set (∀n,η n)}, 
  s1∈B→ s2∈B → ∀{x:∀n,η n}, x∈ s1 ∩ s2 → ∃s3, s3∈B ∧ x∈s3 ∧ s3⊆ s1∩s2 := by
    intro s1 s2 hs1 hs2 x hx
    refine' Exists.elim hs1 _
    intro sets1 hs1
    refine' Exists.elim hs2 _
    intro sets2 hs2
    let sets3:=fun n => (sets1 n) ∩ (sets2 n)
    have p4:setFinProd sets3 ∈ B := by 
      exact mem_def.mpr ⟨sets3,rfl,fun m => openInter (hs1.right m) (hs2.right m) ⟩ 
    have p5:x ∈setFinProd sets3 := by 
      simp ; rw [hs1.left,hs2.left] at hx
      simp at hx ; simp [hx]
    have p6:setFinProd sets3 ⊆ s1 ∩ s2 := by
      refine' setSubsetIff.mpr _
      intro z hz
      simp at hz; rw [hs1.left,hs2.left]; simp
      simp [hz]
    exact ⟨_,p4,p5,p6 ⟩ 
  exact ((basisForSomeSpaceIff B).mp ⟨ p1, p2⟩ )

@[reducible]
instance finProdTopologicalSpace {N:ℕ}{η:Fin N → Type u_1}
[tsη:(n:Fin N)->TopologicalSpace (η n )]:TopologicalSpace (∀n,η n ):=
  choose (finProdTopologicalSpace.aux tsη )

lemma finProdTopologicalSpaceBasis {N:ℕ}{η:Fin N → Type u_1}
(tsη:(n:Fin N)->TopologicalSpace (η n )): ∃tB:topologicalBasis (@finProdTopologicalSpace _ _ tsη ) ,
{s | ∃ l, s = setFinProd l ∧ ∀ (m : Fin N), TopologicalSpace.IsOpen (l m)} = tB.sets :=
  (choose_spec (finProdTopologicalSpace.aux tsη)).left 

lemma finProdOfOpenIsOpen  {N:ℕ}{η:Fin N → Type u_1} 
{tsη:(n:Fin N)->TopologicalSpace (η n )} {l:(n:Fin N)->Set (η n)}
(hl:(n:Fin N)->@IsOpen _ (tsη n) (l n)):
@IsOpen _ (@finProdTopologicalSpace _ _ tsη) (setFinProd l) := by
  refine' Exists.elim (finProdTopologicalSpaceBasis tsη ) _
  intro tB htB
  have p1: (setFinProd l)∈ tB.sets := by
    rw [htB.symm]; simp only [mem_def,setOf]
    exact ⟨l,rfl,hl ⟩ 
  exact tB.sets_forall_open p1

def neighbsFinProd {N:ℕ}{η:Fin N → Type u_1} {x:∀n,η n}
{tsη:(n:Fin N)->TopologicalSpace (η n )} (l:(n:Fin N)->@neighb _ (tsη n) (x n)):
@neighb _ (@finProdTopologicalSpace _ _ tsη) x := by 
  have p1: x∈ setFinProd (fun n => (l n).set) := by
    simp; intro n ; exact (l n).property.left
  have p2: @IsOpen _  (@finProdTopologicalSpace _ _ tsη) (setFinProd (fun n => (l n).set)) :=
    finProdOfOpenIsOpen (fun n=> (l n).property.right)
  exact @neighb.mk _ (@finProdTopologicalSpace _ _ tsη) _ _ ⟨p1,p2 ⟩ 

lemma existsProdNeighbInFinProdSpace {N:ℕ}{η:Fin N → Type u_1} {x:∀n,η n}
[tsη:(n:Fin N)->TopologicalSpace (η n )] (nb:@neighb _ (@finProdTopologicalSpace _ _ tsη) x):
∃(l:(n:Fin N)->@neighb _ (tsη n) (x n)), 
(@neighb.set _ (@finProdTopologicalSpace _ _ tsη) _ (neighbsFinProd l)) 
⊆ @neighb.set _ (@finProdTopologicalSpace _ _ tsη) _ nb := by 
  refine' Exists.elim (finProdTopologicalSpaceBasis tsη) _
  intro tB htB
  refine' Exists.elim (tB.any_open_is_sunion (@neighb.property _ 
    (@finProdTopologicalSpace _ _ tsη) _ nb).right) _
  intro b hb
  let p1:=hb.right ▸ (@neighb.property _ (@finProdTopologicalSpace _ _ tsη) _ nb).left
  simp only [mem_sUnion] at p1
  refine' Exists.elim p1 _
  intro s hs
  let p2:= htB.symm ▸ (setSubsetIff.mp hb.left _ hs.left)
  simp only [mem_def,setOf] at p2
  refine' Exists.elim p2 _
  intro l hl
  let p3:=hl.left ▸ hs.right; simp  at p3
  let l':(n:Fin N) -> @neighb _ (tsη n) (x n) :=
    fun n => ⟨_,p3 n ,hl.right n ⟩ 
  have p4: @neighb.set _ (@finProdTopologicalSpace _ _ tsη) _ (neighbsFinProd l') = setFinProd l :=
    rfl
  have p5:setFinProd l ⊆  @neighb.set _ (@finProdTopologicalSpace _ _ tsη) _ nb := by
    rw [hb.right,hl.left.symm]; refine' setSubsetIff.mpr _
    intro z hz; simp
    exact ⟨_,hs.left,hz ⟩  
  rw [p4.symm] at p5; exact ⟨ _,p5⟩ 

lemma projIsContinuous {N:ℕ}{η:Fin N → Type u_1} [tsη:(n:Fin N)->TopologicalSpace (η n )]
:∀ (n:Fin N), @Continuous _ _ (@finProdTopologicalSpace _ _ tsη  ) (tsη n) 
(fun (x:∀i,η i) => x n) := by
  intro n 
  refine' (@continuousDef _ _ (@finProdTopologicalSpace _ _ tsη  ) (tsη n)).mpr _
  intro s hs
  let sets: (m:Fin N) ->Set (η m) := fun m => 
    if H:m=n 
      then by rw [H]; exact s
      else univ
  have p1: setFinProd sets = PreIm((fun (x:∀n,η n) => x n),s) := by
    refine' setEqIff.mpr _
    intro x
    have mp:x ∈ setFinProd sets -> x ∈ PreIm((fun (x:∀n,η n) => x n),s)  := by
      intro h1; simp; simp at h1
      let p2:=h1 n; simp at p2; exact p2
    have mpr:x∈PreIm((fun (x:∀n,η n) => x n),s) -> x ∈ setFinProd sets := by
      intro h1; simp ; simp at h1
      intro m 
      by_cases c:m=n
      · rw [c]; simp; exact h1
      · simp [c]
    exact ⟨mp,mpr⟩ 
  have p2: @IsOpen _ (@finProdTopologicalSpace _ _ tsη) (setFinProd sets) := by
    refine' Exists.elim (choose_spec (finProdTopologicalSpace.aux tsη)).left _
    intro tB htB
    have p3:setFinProd sets∈ tB.sets := by 
      rw [htB.symm]; refine' ⟨sets,rfl,_ ⟩ 
      intro m
      by_cases c:m=n
      · rw [c]; simp; exact hs
      · simp [c]; exact univIsOpen
    exact tB.sets_forall_open p3
  rw [p1.symm]; exact p2

lemma finProdSpaceUniversalProperty' {N:ℕ}{η:Fin N → Type u_1} (tsη:(n:Fin N)->TopologicalSpace (η n ))
[TopologicalSpace α](f:α ->(∀n,η n)): @Continuous _ _ _ (@finProdTopologicalSpace _ _ tsη ) f ↔ 
∀(n:Fin N), Continuous (((fun (x:∀n,η n) => x n))∘f) := by 
  have mp: @Continuous _ _ _ (@finProdTopologicalSpace _ _ tsη ) f ->
  ∀(n:Fin N), Continuous (((fun (x:∀n,η n) => x n))∘f)  := by
    intro h1 n;
    exact @continuousComp _ _ _ _ (@finProdTopologicalSpace _ _ tsη )
      _ _ _ (projIsContinuous n) h1
  have mpr: (∀(n:Fin N), Continuous (((fun (x:∀n,η n) => x n))∘f)) -> 
  @Continuous _ _ _ (@finProdTopologicalSpace _ _ tsη ) f := by
    intro h1
    refine' Exists.elim (choose_spec (finProdTopologicalSpace.aux tsη)).left _
    intro tB htB
    have p1:∀{s:Set ((∀n,η n))}, s∈tB.sets -> IsOpen (PreIm(f,s)) := by
      intro s hs; rw [htB.symm] at hs; simp at hs
      refine' Exists.elim hs _
      intro sets hsets
      have p2: PreIm(f,s) = ⋂₀ Im(fun m=>PreIm(((fun (x:∀i,η i) => x m)∘f),sets m),univ) := by
        refine' setEqIff.mpr _
        intro x ; rw [hsets.left]; simp
      let fs:= Finite.toFinset
        ((Finite.image _ finite_univ):Im(fun m=>PreIm(((fun (x:∀i,η i) => x m)∘f),sets m),univ).Finite )
      have p3:fs.toSet = Im(fun m=>PreIm(((fun (x:∀i,η i) => x m)∘f),sets m),univ):= by simp
      have p4:∀ {si:Set α},si∈ fs.toSet -> IsOpen si := by
        intro si hsi; simp at hsi
        refine' Exists.elim hsi _
        intro nn hnn; rw [hnn.symm]
        exact continuousDef.mp (h1 nn)  (hsets.right nn)
      rw [p2,p3.symm]; exact finsetOpenInter p4
    refine' (@continuousDef _ _ _ (@finProdTopologicalSpace _ _ tsη ) _).mpr _
    intro s hs
    refine' Exists.elim (tB.any_open_is_sunion hs) _
    intro b hb; rw [hb.right,preImSUnion]
    have p2:∀{t:Set α}, t∈ Im(fun x => PreIm(f,x),b) -> IsOpen t := by
      intro t ht; simp only [mem_image] at ht
      refine' Exists.elim ht _
      intro r hr; rw [hr.right.symm]
      exact p1 (setSubsetIff.mp hb.left _ hr.left)
    exact openSUnion p2
  exact ⟨mp,mpr⟩ 

lemma finProdTopologyEqSubspaceTopology {N:ℕ}{η:Fin N → Type u_1} [tsη:(n:Fin N)->TopologicalSpace (η n )]
(sets:(n:Fin N)->Set (η n )) (h:Nonempty (∀ n, Subtype (sets n))):
@Homeomorph _ _ (@finProdTopologicalSpace _ (fun n => Subtype (sets n)) 
(fun n=> @instTopologicalSpaceSubtype _ (sets n) (tsη n)))  
(@instTopologicalSpaceSubtype _ (setFinProd sets) (@finProdTopologicalSpace _ _ tsη)) :=by
  let toEquiv_1:Equiv (∀ n, Subtype (sets n)) (Subtype (setFinProd sets)):={
    toFun:=fun x =>⟨fun m =>(x m).val ,fun m =>(x m).property⟩ 
    invFun:=Function.invFun fun x =>⟨fun m =>(x m).val ,fun m =>(x m).property⟩
    left_inv:= by 
      refine' Function.leftInverse_invFun _
      simp only [Function.Injective]
      intro x1 x2 H
      let x1map:= x1
      let x2map:= x2
      replace H:=congrArg (Subtype.val) H; simp at H
      have p1:x1map = x2map := by
        refine' funcEqIff.mpr _
        intro a; 
        calc 
          x1map a = ⟨(x1map a).val,_ ⟩  := rfl
          _ = ⟨(x2map a).val, _ ⟩  := by simp_rw [congrFun H a]
      simp_rw [p1]
    right_inv := by      
      refine' Function.rightInverse_invFun _
      simp only [Function.Surjective]
      intro y 
      let p1:=y.property; simp only [setFinProd,setOf] at p1
      refine' ⟨fun m => ⟨ y.val m,p1 m⟩ , _ ⟩ 
      simp}
  have p1:Im(fun x => (toEquiv_1.toFun x).val,univ) ⊆ setFinProd sets := by
    refine' setSubsetIff.mpr _
    intro y hy; simp only [mem_image] at hy
    refine' Exists.elim hy _
    intro x hx; rw [hx.right.symm];simp   
  have  continuous_toFun :@Continuous _ _ 
    (@finProdTopologicalSpace _ (fun n => Subtype (sets n)) 
    (fun n=> @instTopologicalSpaceSubtype _ (sets n) (tsη n)))   
    (@instTopologicalSpaceSubtype _ (setFinProd sets) (@finProdTopologicalSpace _ _ tsη))  
    toEquiv_1.toFun := by
    refine' @continuousRestrictCodomain _ _ 
      (@finProdTopologicalSpace _ (fun n => Subtype (sets n)) 
      (fun n=> @instTopologicalSpaceSubtype _ (sets n) (tsη n))) 
      (@finProdTopologicalSpace _ _ tsη)  _ 
      ((@finProdSpaceUniversalProperty' _ _ _ tsη 
      (@finProdTopologicalSpace _ (fun n => Subtype (sets n)) 
      (fun n=> @instTopologicalSpaceSubtype _ (sets n) (tsη n)))   _).mpr _) (setFinProd sets) p1
    intro n; 
    have p2:(fun (a:(∀n,η n) ) => a n) ∘ 
    (fun (x:(∀ n, Subtype (sets n))) => fun m =>(x m).val)
    = Subtype.val ∘ (fun (x:(∀ n, Subtype (sets n))) =>x n) := by
      refine' funcEqIff.mpr _
      intro x; simp
    rw [p2]
    exact @continuousComp _ _ _ (tsη n) (@instTopologicalSpaceSubtype _ 
    (sets n) (tsη n)) (@finProdTopologicalSpace _ (fun n => Subtype (sets n)) 
    (fun n=> @instTopologicalSpaceSubtype _ (sets n) (tsη n))) _ _ 
      (@subtypeValIsContinuous _ (tsη n) _) (@projIsContinuous  _ _
        (fun n=> @instTopologicalSpaceSubtype _ (sets n) (tsη n)) n)
  have continuous_invFun: @Continuous _ _ 
    (@instTopologicalSpaceSubtype _ (setFinProd sets) (@finProdTopologicalSpace _ _ tsη))  
    (@finProdTopologicalSpace _ (fun n => Subtype (sets n)) 
    (fun n=> @instTopologicalSpaceSubtype _ (sets n) (tsη n)))
    toEquiv_1.invFun := by
    let g: (Subtype (setFinProd sets))->(∀ n, Subtype (sets n)) := 
      fun y=> fun m=>⟨y.val m, (y.property:∀ (m:Fin N), y.val m ∈ sets m) m ⟩
    have p2:g=toEquiv_1.invFun := by
      refine' funcEqIff.mpr _
      intro y ; 
      rw [(congrArg toEquiv_1.invFun (by simp:toEquiv_1.toFun (g y) =y)).symm,
        toEquiv_1.left_inv]
    rw [p2.symm]
    refine' (@finProdSpaceUniversalProperty' _ _ _ 
      (fun n=> @instTopologicalSpaceSubtype _ (sets n) (tsη n)) 
        (@instTopologicalSpaceSubtype _ (setFinProd sets) 
        (@finProdTopologicalSpace _ _ tsη))  _ ).mpr _
    intro n
    let g':(Subtype (setFinProd sets))->η n :=
      fun y => y.val n
    have p3  :  Im(g',univ)⊆  sets n := by
      refine' setSubsetIff.mpr _
      intro y hy; rw [mem_image] at hy
      refine' Exists.elim hy _
      intro y' hy' ; rw [hy'.right.symm]
      exact y'.property n
    have p4 : @Continuous _ _ (@instTopologicalSpaceSubtype _ (setFinProd sets) 
      (@finProdTopologicalSpace _ _ tsη)) (tsη n)  g' := 
        @continuousComp _ _ _ (tsη n)  (@finProdTopologicalSpace _ _ tsη)  
          (@instTopologicalSpaceSubtype _ (setFinProd sets)   (@finProdTopologicalSpace _ _ tsη)) 
          ((fun (x:∀n,η n) => x n)) (Subtype.val)  (projIsContinuous n) 
          (@subtypeValIsContinuous _ (@finProdTopologicalSpace _ _ tsη) _)
    replace p4:=@continuousRestrictCodomain _ _  
      (@instTopologicalSpaceSubtype _ (setFinProd sets) (@finProdTopologicalSpace _ _ tsη))  (tsη n) 
      _ p4 _ p3
    have p5:∀{x:(Subtype (setFinProd sets))}, g' x ∈ sets n :=  by
      intro x ; exact x.property n
    have p6: (fun x => ⟨ g' x,p5 ⟩) = ((fun (x:∀n,Subtype (sets n) ) => x n) ∘ g) := by 
      refine' funcEqIff.mpr _
      intro y; simp
    rw [p6.symm]; exact p4
  exact @Homeomorph.mk  _ _ (@finProdTopologicalSpace _ (fun n => Subtype (sets n)) 
    (fun n=> @instTopologicalSpaceSubtype _ (sets n) (tsη n)))  
    (@instTopologicalSpaceSubtype _ (setFinProd sets) (@finProdTopologicalSpace _ _ tsη)) 
    toEquiv_1 continuous_toFun continuous_invFun

lemma finProdTopologyEqProdTopology {α γ:Type u_1} [ts1:TopologicalSpace α] [ts2:TopologicalSpace γ] :
@Homeomorph _ _ (@instTopologicalSpaceProd _ _ ts1 ts2) 
(@finProdTopologicalSpace 2 (fun (m:Fin 2)=>(match m with | 0=>α | 1=>γ)) 
(fun (m:Fin 2)=>(match m with | 0=>ts1 | 1=>ts2))) :=  by
  let η :=fun (m:Fin 2)=>(match m with | 0=>α | 1=>γ)
  let to_equiv :Equiv (α×γ) (∀n, η n) := {
    toFun :=fun x=>  fun m=>(match m with | 0=>x.1 | 1=>x.2)
    invFun := fun y => ⟨y 0,y 1 ⟩ 
    left_inv := by 
      simp only [Function.LeftInverse]
      intro x ;rfl
    right_inv:= by 
      simp only [Function.RightInverse]
      intro y;simp
      refine' funcEqIff.mpr _
      intro m; 
      match m with 
       | 0=> rfl
       | 1=> rfl}
  have continuous_toFun :@Continuous _ _ (@instTopologicalSpaceProd _ _ ts1 ts2)
    (@finProdTopologicalSpace 2 (fun (m:Fin 2)=>(match m with | 0=>α | 1=>γ)) 
      (fun (m:Fin 2)=>(match m with | 0=>ts1 | 1=>ts2))) to_equiv.toFun :=  by
    refine' (@finProdSpaceUniversalProperty' _ _ (fun (m:Fin 2)=>(match m with | 0=>α | 1=>γ)  )
      (fun (m:Fin 2)=>(match m with | 0=>ts1 | 1=>ts2)) (@instTopologicalSpaceProd _ _ ts1 ts2) _).mpr _
    intro m
    match m with
    | 0=>
      have p1: ((fun (x:∀i,η i) => x 0) ∘ to_equiv.toFun) = fun (x:α×γ) => x.1 := by 
        refine' funcEqIff.mpr _
        intro x; simp; rfl
      rw [p1];  exact @continuous_fst _ _ ts1 ts2
    | 1=>
      have p1: ((fun (x:∀i,η i) => x 1) ∘ to_equiv.toFun) = fun (x:α×γ) => x.2 := by 
        refine' funcEqIff.mpr _
        intro x; simp; rfl
      rw [p1];  exact @continuous_snd _ _ ts1 ts2     
  have continuous_invFun :@Continuous _ _  
    (@finProdTopologicalSpace 2 (fun (m:Fin 2)=>(match m with | 0=>α | 1=>γ)) 
    (fun (m:Fin 2)=>(match m with | 0=>ts1 | 1=>ts2))) 
    (@instTopologicalSpaceProd _ _ ts1 ts2) to_equiv.invFun := 
    @Continuous.prod_mk _ _ _ ts1 ts2 
      (@finProdTopologicalSpace 2 (fun (m:Fin 2)=>(match m with | 0=>α | 1=>γ)) 
      (fun (m:Fin 2)=>(match m with | 0=>ts1 | 1=>ts2))) _ _ 
      (@projIsContinuous _ (fun (m:Fin 2)=>(match m with | 0=>α | 1=>γ)) 
      (fun (m:Fin 2)=>(match m with | 0=>ts1 | 1=>ts2)) 0)  
      (@projIsContinuous _ (fun (m:Fin 2)=>(match m with | 0=>α | 1=>γ)) 
      (fun (m:Fin 2)=>(match m with | 0=>ts1 | 1=>ts2)) 1)  
  exact @Homeomorph.mk  _ _ (@instTopologicalSpaceProd _ _ ts1 ts2) 
    (@finProdTopologicalSpace 2 (fun (m:Fin 2)=>(match m with | 0=>α | 1=>γ)) 
    (fun (m:Fin 2)=>(match m with | 0=>ts1 | 1=>ts2)))
    to_equiv continuous_toFun continuous_invFun 

lemma finProdTopologyPermEqOrig {N:ℕ}{η:Fin N → Type u_1} {j:Fin N->Fin N} [Nonempty (Fin N)]
(tsη:(n:Fin N)->TopologicalSpace (η n ))  (h:Function.Bijective j) :
@Homeomorph _ _ (@finProdTopologicalSpace _ η tsη) 
(@finProdTopologicalSpace _ _ (fun m=>tsη (j m))) := by 
  let to_equiv:Equiv ((∀n,η n)) (∀ m,η (j m)) := {
    toFun := fun x =>fun m=> x (j m)
    invFun := fun x =>fun m=>
      cast (congrArg η (Eq.trans (congrFun (funcSurjRightInvComp h.right) m) (id.def m)) ) 
      (x ((Function.invFun j) m))
    left_inv := by
      simp only [Function.LeftInverse]
      intro x; 
      let mapx := x
      refine' funcEqIff.mpr _
      intro m; 
      let p1:=(congrFun (funcSurjRightInvComp h.right) m)
      simp at p1; 
      let p2:=congrArg η  (congrFun (funcSurjRightInvComp h.right) m)
      rw [id] at p2
      have p3: HEq (mapx ((j ∘ Function.invFun j) m)) ( mapx m) 
          := congr_arg_heq mapx p1
      have p4: HEq (cast p2 (mapx (j (Function.invFun j m)))) (mapx (j (Function.invFun j m))):= 
          cast_heq _ _
      exact heq_iff_eq.mp ( HEq.trans  p4 p3)
    right_inv := by
      simp only [Function.RightInverse]
      intro x; 
      let mapx :=x
      simp; refine' funcEqIff.mpr _
      intro m; 
      let p1:=(congrFun (funcLeftInvInjComp h.left) m)
      simp at p1; 
      let p2:=congrArg η  (congrFun (funcSurjRightInvComp h.right) (j m))
      rw [id] at p2
      have p3 := congr_arg_heq mapx p1
      have p4: HEq (cast p2 (mapx (Function.invFun j (j m)))) (mapx (Function.invFun j (j m))):= 
          cast_heq _ _
      exact heq_iff_eq.mp ( HEq.trans  p4 p3)  }
  have continuous_toFun :@Continuous _ _
    (@finProdTopologicalSpace _ η tsη) (@finProdTopologicalSpace _ _ (fun m=>tsη (j m)))
    to_equiv.toFun := by
      refine' (@finProdSpaceUniversalProperty' _ _ _ (fun m=>tsη (j m)) 
        (@finProdTopologicalSpace _ η tsη) _).mpr _
      intro l;
      have p1: (fun xx=>xx l) ∘ to_equiv.toFun = (fun xx=> xx (j l)) := by
        refine' funcEqIff.mpr _
        intro x; simp
      rw [p1]; exact @projIsContinuous _ _ tsη (j l)
  have continuous_invFun : @Continuous _ _
    (@finProdTopologicalSpace _ _ (fun m=>tsη (j m))) (@finProdTopologicalSpace _ η tsη) 
    to_equiv.invFun := by
      refine' (@finProdSpaceUniversalProperty' _ _ _ tsη
        (@finProdTopologicalSpace _ _ (fun m=>tsη (j m))) _).mpr _
      intro l;     
      have p1 (l':Fin N): (fun xx => xx (j l')) ∘ to_equiv.invFun = fun xx => xx l' := by
        refine' funcEqIff.mpr _
        intro y; simp
        let p1:=(congrFun (funcSurjRightInvComp h.right) (j l'))
        simp at p1; 
        let p2:=congrArg η  (congrFun (funcSurjRightInvComp h.right) (j l'))
        rw [id] at p2
        have p3: (Function.invFun j (j l')) = l'  := by
          exact congrFun (funcLeftInvInjComp h.left) l'
        have p4: HEq (y ((Function.invFun j (j l')))) ( y l') 
          := congr_arg_heq y p3
        have p5: HEq (cast p2 (y (Function.invFun j (j l')))) (y  (Function.invFun j (j l'))):= 
          cast_heq _ _
        simp at p4
        exact heq_iff_eq.mp ( HEq.trans  p5 p4)
      replace p1:=p1 ((Function.invFun j) l)
      let p2:=congrFun (funcSurjRightInvComp h.right) l
      simp at p2; let p2':=congrArg η p2
      have p3:HEq 
        ((fun xx => xx (j (Function.invFun j l))):((∀n,η n)) -> η (j (Function.invFun j l)) )  
        ((fun xx => xx l):((∀n,η n)) -> η l) := 
        congr_arg_heq (fun (nn:Fin N) (xx:∀n,η n) => xx nn) p2
      have p4: HEq ((fun (xx) => xx l )∘ to_equiv.invFun) 
        ((fun xx => xx (j (Function.invFun j l))) ∘ to_equiv.invFun) := by
        let tempF {γ:Type u_1} : (((∀n,η n))->γ)->
          ((∀ m, η (j m))->((∀n,η n)))->((∀ m, η (j m)))->γ:=
          fun f =>fun g => f∘g
        have p6 {γ1 γ2:Type u_1} {f1:((∀n,η n))->γ1} {f2:((∀n,η n))->γ2}(h1p6:γ1=γ2):
          (HEq f1 f2)-> HEq (tempF f1) (tempF f2) := by
          intro h2p6
          cases h1p6
          replace h2p6:=heq_iff_eq.mp h2p6
          exact heq_iff_eq.mpr (congrArg tempF h2p6)
        replace p6:=p6 p2' p3
        exact (HEQ.congr_fun_heq'  to_equiv.invFun (by rw [p2']) p6).symm
      have p5:@Continuous _ _ (@finProdTopologicalSpace _ _ (fun m=>tsη (j m))) _ 
        ((fun xx => xx (j (Function.invFun j l))) ∘ to_equiv.invFun) := by
        rw [p1]
        exact @projIsContinuous  _ _ (fun m=>tsη (j m))  (Function.invFun j l)
      have p6 {n1 n2:Fin N} 
        {f1:((∀ m, η (j m)))->η n1} {f2:((∀ m, η (j m)))->η n2} 
        (h1p6:n1=n2) (h2p6:HEq f1 f2) 
        (h3p6:@Continuous _ _ (@finProdTopologicalSpace _ _ (fun m=>tsη (j m))) (tsη n1) f1) :
        @Continuous _ _ (@finProdTopologicalSpace _ _ (fun m=>tsη (j m))) (tsη n2) f2 := by 
        cases h1p6; replace h2p6:= heq_iff_eq.mp h2p6
        rw [h2p6.symm]; exact h3p6
      exact p6 p2 p4.symm p5
  exact @Homeomorph.mk  _ _ (@finProdTopologicalSpace _ η tsη) 
    (@finProdTopologicalSpace _ _ (fun m=>tsη (j m)))  
    to_equiv continuous_toFun continuous_invFun 

lemma basisProdIsFInProdBasis {N:ℕ}{η:Fin N → Type u_1} 
[tsη:(n:Fin N)->TopologicalSpace (η n )] (tbη:(n:Fin N)->topologicalBasis (tsη n)):
∃tB':topologicalBasis (@finProdTopologicalSpace _ _ tsη), tB'.sets=
{s|∃l: (n:Fin N) ->Set (η n),s=setFinProd l ∧ ∀m:Fin N, (l m)∈(tbη m).sets } := by 
  refine' Exists.elim (finProdTopologicalSpaceBasis tsη) _
  intro tB htB
  let tB':topologicalBasis (@finProdTopologicalSpace _ _ tsη) :={
    sets:={s|∃l: (n:Fin N) ->Set (η n),s=setFinProd l ∧ ∀m:Fin N, (l m)∈(tbη m).sets }
    sets_forall_open:= by
      intro s hs
      have p1: s∈tB.sets := by
        rw [htB.symm]; simp; simp at hs
        refine' Exists.elim hs _
        intro l hl
        refine' ⟨_,hl.left,_ ⟩ 
        intro m
        exact (tbη m).sets_forall_open (hl.right m)
      exact tB.sets_forall_open p1
    any_open_is_sunion:= by
      intro s hs
      let hB1:=tB.any_open_is_sunion hs
      refine' Exists.elim hB1 _
      intro B1 hB1
      let f:Subtype B1 -> Set (Set (∀ n , η n)) := 
        fun x=>
        {s|∃l: (n:Fin N) ->Set (η n),s=setFinProd l ∧ ∀m:Fin N, (l m)∈
        choose ((tbη m).any_open_is_sunion ((choose_spec (mem_setOf_eq.to_iff.mp 
        ((Eq.subst htB.symm (setSubsetIff.mp hB1.left _ x.property))
        :x.val ∈ {s | ∃ l, s = setFinProd l ∧ ∀ (m : Fin N), 
        TopologicalSpace.IsOpen (l m)} ))).right m)) }
      let B:=⋃₀ Im(f,(univ:Set (Subtype B1)))
      have p1:B⊆ {s | ∃ l, s = setFinProd l ∧ ∀ (m : Fin N), l m ∈ (tbη m).sets} := by
        refine' setSubsetIff.mpr _
        intro s  hs; 
        refine' Exists.elim hs _
        intro sb hsb
        let p2:=hsb.left; simp only [mem_image] at p2
        refine' Exists.elim p2 _
        intro t p2
        replace p2:=p2.right.symm ▸ hsb.right; simp at p2
        refine' Exists.elim p2 _
        intro l p2; simp; refine' ⟨l,p2.left,_ ⟩ 
        intro m
        let p4:= choose_spec ((tbη m).any_open_is_sunion ((choose_spec (mem_setOf_eq.to_iff.mp 
          ((Eq.subst htB.symm (setSubsetIff.mp hB1.left _ t.property))
          :t.val ∈ {s | ∃ l, s = setFinProd l ∧ ∀ (m : Fin N), 
          TopologicalSpace.IsOpen (l m)} ))).right m))
        exact setSubsetIff.mp p4.left _ (p2.right m)
      have p2: s = ⋃₀ B := by
        refine' setEqIff.mpr _
        intro x
        have mp: (x∈s) -> x∈ (⋃₀ B) := by 
          intro h1; rw [hB1.right] at h1
          simp only [mem_sUnion] at h1
          refine' Exists.elim h1 _
          intro t ht
          have p3:∃t':Set (∀ n, η n) , t'∈ f ⟨_,ht.left⟩∧ x∈t'  := by
            let p4:= (choose_spec (mem_setOf_eq.to_iff.mp ((Eq.subst htB.symm 
              (setSubsetIff.mp hB1.left _ ht.left)) :
              t∈ {s | ∃ l, s = setFinProd l ∧ ∀ (m : Fin N), TopologicalSpace.IsOpen (l m)} )))
            let p5:=p4.left ▸ ht.right; simp at p5
            let p6:=(choose_spec (mem_setOf_eq.to_iff.mp ((Eq.subst htB.symm 
              (setSubsetIff.mp hB1.left _ ht.left)) 
              :t∈ {s | ∃ l, s = setFinProd l ∧ ∀ (m : Fin N), TopologicalSpace.IsOpen (l m)} )))
            set sets_found:= choose (mem_setOf_eq.to_iff.mp ((Eq.subst htB.symm 
              (setSubsetIff.mp hB1.left _ ht.left)) 
              :t∈ {s | ∃ l, s = setFinProd l ∧ ∀ (m : Fin N), TopologicalSpace.IsOpen (l m)} ))
            let setst':=  fun m=>choose (mem_sUnion.mp ((choose_spec  
              ((tbη m).any_open_is_sunion ((p6.right m)))  ).right.subst (p5 m)))
            have p7:x∈setFinProd setst'  := by 
              simp
              exact fun m=>(choose_spec (mem_sUnion.mp ((choose_spec  
                ((tbη m).any_open_is_sunion ((p6.right m)))  ).right.subst (p5 m)))).right
            let p8:= fun m=>(choose_spec (mem_sUnion.mp ((choose_spec  
                ((tbη m).any_open_is_sunion ((p6.right m)))  ).right.subst (p5 m)))).left
            refine' ⟨_,⟨setst',rfl,p8 ⟩ ,p7 ⟩ 
          refine' Exists.elim p3 _
          intro t' ht'
          have p4: t' ∈ B := by 
            refine' (mem_sUnion).mpr _
            refine' ⟨_,_,ht'.left ⟩ 
            rw [mem_image]
            exact ⟨⟨_,ht.left⟩,by simp,rfl ⟩ 
          refine' mem_sUnion.mpr _
          exact ⟨_,p4,ht'.right ⟩ 
        have mpr: x∈ (⋃₀ B)->(x∈s)   := by
          intro h1; rw [mem_sUnion] at h1
          refine' Exists.elim h1 _
          intro t ht; rw [mem_sUnion] at ht
          refine' Exists.elim ht.left _
          intro t' ht'
          rw [mem_image] at ht'
          refine' Exists.elim ht'.left _
          intro b hb
          have p1:∀{r:Set (∀ n , η n)}, r∈t' ->r⊆b.val := by 
            intro r hr; refine' setSubsetIff.mpr _
            intro z hz; rw [hb.right.symm] at hr; simp at hr
            refine' Exists.elim hr _
            intro l hl; rw [hl.left] at hz
            let pb:= (mem_setOf_eq.to_iff.mp 
              ((Eq.subst htB.symm (setSubsetIff.mp hB1.left _ b.property))
              :b.val ∈ {s | ∃ l, s = setFinProd l ∧ ∀ (m : Fin N), 
              TopologicalSpace.IsOpen (l m)} ))
            set setsb:=choose pb
            let p2:↑b = setFinProd setsb ∧ ∀ (m : Fin N), TopologicalSpace.IsOpen (setsb m)
              :=choose_spec pb
            let p3:=fun (m:Fin N) =>choose_spec ((tbη m).any_open_is_sunion (p2.right m))
            simp at hz
            have p4:∀ (m : Fin N), z m ∈ setsb m := by
              intro m; rw [(p3 m).right]
              rw [mem_sUnion]; exact ⟨_,hl.right m,hz m ⟩ 
            rw [p2.left]; exact p4
          replace p1:=setSubsetIff.mp  (p1 ht'.right) _ ht.right
          rw [hB1.right,mem_sUnion]; exact ⟨_,b.property,p1 ⟩ 
        exact ⟨mp,mpr ⟩ 
      exact ⟨_,p1,p2 ⟩ }
  exact ⟨tB',rfl ⟩ 

@[reducible]
instance finProdFstCountableIfAllFstCountable  {N:ℕ}{η:Fin N → Type u_1} [inst:Nonempty (Fin N)]
[tsη:(n:Fin N)->TopologicalSpace (η n )] [fstη:(n:Fin N)->@fstCountable _ (tsη n )]:
@fstCountable _ (@finProdTopologicalSpace _ _ tsη) := by 
  have p1:∀ (x:(∀n,η n)), ∃ (nbB:@neighbBasis _ (@finProdTopologicalSpace _ _ tsη) x) ,
    (@neighbBasis.neighbs _ (@finProdTopologicalSpace _ _ tsη) _ nbB).atMostCountable := by
    intro x
    let f:ℕ → @neighb _ (@finProdTopologicalSpace _ _ tsη) x :=
      fun (k:Nat) => neighbsFinProd
      (fun n=> (choose (choose_spec (@existsNestedNeighbBasis _ _ (fstη n) 
      (x n)))) k )
    have p2:(∀ (nb : @neighb _ (@finProdTopologicalSpace _ _ tsη) x), 
      ∃ t, t ∈ Im(f,univ) ∧ (@neighb.set _ (@finProdTopologicalSpace _ _ tsη) _ t) 
      ⊆ @neighb.set _ (@finProdTopologicalSpace _ _ tsη) _ nb) := by
      intro nb_given
      refine' Exists.elim (existsProdNeighbInFinProdSpace nb_given) _
      intro l_nb_shrinked h_nb_shrinkded
      let lM:Fin N-> Nat:= fun (n:Fin N) =>choose ((mem_image _ _ _).mp 
        ((choose_spec (choose_spec (@existsNestedNeighbBasis _ _ (fstη n) 
        (x n)))).left.subst (choose_spec ((choose (@existsNestedNeighbBasis _ _ 
        (fstη n) (x n))).exists_contained (l_nb_shrinked n))).left))
      let lM':= fun (n:Fin N) => ((lM n):Real)
      have p3:((List.finRange N).map lM') ≠ [] := by 
        by_contra hc
        replace hc:=congrArg List.length hc
        have p4: (List.map lM' (List.finRange N)).length = N := by
          rw [List.length_map]; simp
        rw [p4] at hc; simp at hc
        match inst with
        |.intro a =>
          match a with 
          |.mk val property =>
            rw [hc] at property; simp at property
      refine' Exists.elim (@SUP_INF.maxIsReachable ((List.finRange N).map lM') p3) _
      intro k hk
      refine' Exists.elim hk _
      intro p4 hk;have p4':=p4; 
      rw [List.length_map] at p4; simp at p4
      have p5:∀(i:Fin N), lM i ≤ lM ⟨k,p4⟩ := by 
        intro i
        have p6: ((lM i):Real) ∈ ((List.finRange N).map lM') := by 
          rw [List.mem_map];exact ⟨i,by simp,rfl ⟩ 
        replace p6:=@SUP_INF.maxIsGreatest ((List.finRange N).map lM') _ p6
        rw [hk.symm,EReal.coe_le_coe_iff] at p6; 
        rw [List.length_map] at p4'
        have p7: (List.map lM' (List.finRange N))[k] = ((lM ⟨k,p4⟩):Real) := by 
          rw [listMapNEqFN]
          have p9: (List.finRange N)[k] = ⟨k,p4 ⟩ := by simp
          rw [p9]
        rw [p7] at p6; 
        have p8 {n1 n2:Nat} :(n1:Real) ≤ (n2:Real) -> n1≤ n2 := by
          intro h1; simp at h1; exact h1
        exact p8 p6
      set M:=lM ⟨k,p4⟩
      have p6: f M ∈ Im(f,univ) := by 
        rw [mem_image]; exact ⟨M,by simp, rfl ⟩ 
      refine' ⟨_,p6,subset_trans (setSubsetIff.mpr _) h_nb_shrinkded ⟩ 
      intro z hz; simp [neighbsFinProd]
      intro n
      let p7:=(@existsNestedNeighbBasis _ _ (fstη n) (x n))
      let p8:= (choose_spec (choose_spec p7))
      set fn:= choose (choose_spec p7)
      set nBn:=choose p7
      let p9:=choose_spec (nBn.exists_contained (l_nb_shrinked n))
      set set_contained:= choose (nBn.exists_contained (l_nb_shrinked n))
      let p10:=(choose_spec ((mem_image _ _ _).mp 
        (p8.left.subst p9.left))).right
      refine' setSubsetIff.mp p9.right _ _; rw [p10.symm]
      let rec p11: ∀ (nn1 nn2:Nat), (nn1≤nn2)->(fn nn2).set ⊆ (fn nn1).set := by
        intro nn1 nn2 hnn 
        match nn2 with 
        | 0 =>
          simp at hnn; rw [hnn]
        | .succ nn2' =>
          by_cases c:nn1 = Nat.succ nn2'
          · rw [c]
          · replace c:= Nat.lt_succ_iff.mp (hnn.lt_of_ne c)
            let p12:= p11 _ _ c
            calc
              _ ⊆ _ := p8.right _
              _ ⊆ _ :=p12
      replace p11:=p11 _ _ (p5 n)
      refine' setSubsetIff.mp p11 _ _
      have p12:∀nn,(z∈(@neighb.set _ (@finProdTopologicalSpace _ _ tsη) _ (f nn)) )
        -> z n∈ (fn nn ).set := by
        intro nn hnn;
        simp only [neighbsFinProd,setFinProd,mem_def,setOf] at hnn
        exact hnn n
      exact p12 _ hz
    let nbB :=@neighbBasis.mk _ (@finProdTopologicalSpace _ _ tsη) _ (Im(f,univ)) p2
    exact ⟨nbB, f ,rfl ⟩ 
  exact @fstCountable.mk _ (@finProdTopologicalSpace _ _ tsη) p1

@[reducible]
instance finProdHausdorffIfAllHausdorff  {N:ℕ}{η:Fin N → Type u_1} 
[tsη:(n:Fin N)->TopologicalSpace (η n )] [hsη:(n:Fin N)->@HausdorffSpace _ (tsη n )]:
@HausdorffSpace _ (@finProdTopologicalSpace _ _ tsη) := by 
  have p1:(∀ {x y : (∀n,η n)}, x ≠ y → 
  ∃(u1:@neighb _ (@finProdTopologicalSpace _ _ tsη) x)(u2:@neighb _ (@finProdTopologicalSpace _ _ tsη) y), 
  @neighb.set _ (@finProdTopologicalSpace _ _ tsη) _ u1 
  ∩ @neighb.set _ (@finProdTopologicalSpace _ _ tsη) _ u2 = ∅) := by
    intro x y hxy
    have p2:∃n:Fin N, x n ≠ y n := by
      by_contra hc
      push_neg at hc
      simp at hc hxy
      exact hxy (funcEqIff.mpr hc)
    refine' Exists.elim p2 _
    intro n hn
    let p3:=(hsη n).property hn
    refine' Exists.elim p3 _
    intro u1 p3
    refine' Exists.elim p3 _
    intro u2 p3
    let lx:(m:Fin N)->@neighb _ (tsη m) (x m) := by
      intro m 
      by_cases c:n=m
      · subst c; exact u1
      · exact ⟨univ,by simp ,univIsOpen ⟩ 
    let ly:(m:Fin N)->@neighb _ (tsη m) (y m) := by
      intro m 
      by_cases c:n=m
      · subst c; exact u2
      · exact ⟨univ,by simp ,univIsOpen ⟩ 
    refine' ⟨neighbsFinProd lx,neighbsFinProd ly, _ ⟩ 
    by_contra hc
    replace hc:=setNonemptyIff.mpr hc
    simp only [Set.Nonempty] at hc
    refine' Exists.elim hc _
    intro z hz; simp [neighbsFinProd] at hz
    let hz1:=hz.left n; simp at hz1
    let hz2:=hz.right n; simp at hz2
    replace hz:=setNonemptyIff.mp
      (nonempty_def.mpr ⟨ _, (mem_inter hz1 hz2)⟩ )
    exact hz p3
  exact @HausdorffSpace.mk _ (@finProdTopologicalSpace _ _ tsη) p1
      
@[reducible]
instance finProdSndCountableIfAllSndCountable  {N:ℕ}{η:Fin N → Type u_1} [inst : Nonempty (Fin N)]
[tsη:(n:Fin N)->TopologicalSpace (η n )] [sndη:(n:Fin N)->@sndCountable _ (tsη n )]:
@sndCountable _ (@finProdTopologicalSpace _ _ tsη) := by
  let basisη:=fun (n:Fin N) =>(choose (sndη n).property)
  let setη := fun (n:Fin N) =>(choose (sndη n).property).sets
  let sethη := fun (n:Fin N) =>(choose_spec (sndη n).property)
  let p1:=finProdOfCountable setη sethη
  set lset:={l: (n: Fin N)->Set (η n) | ∀ (m), l m ∈ setη m} 
  let tBh:=choose_spec (basisProdIsFInProdBasis  basisη)
  set tB:= choose (basisProdIsFInProdBasis  basisη)
  have p2:tB.sets⊆Im(setFinProd,lset) := by
    refine' setSubsetIff.mpr _
    intro s hs; rw [tBh] at hs; 
    simp only [mem_def,setOf] at hs
    refine' Exists.elim hs _
    intro l hl; simp only [mem_image]
    refine' ⟨l,_,hl.left.symm ⟩ 
    simp only [mem_def,setOf]
    exact hl.right
  have p3: Im(setFinProd,lset) ⊆ tB.sets := by
    refine' setSubsetIff.mpr _ 
    intro s hs; rw [tBh]
    simp only [mem_def,setOf]
    simp only [mem_image] at hs
    refine' Exists.elim hs _
    intro l hl; simp only [mem_def,setOf] at hl
    exact ⟨_,hl.right.symm,hl.left ⟩ 
  let p4:=setEqMpr p2 p3
  have p5:tB.sets.atMostCountable := by
    rw [p4];exact imageOfCountable _ p1
  exact @sndCountable.mk _ (@finProdTopologicalSpace _ _ tsη) ⟨_,p5⟩ 

lemma disjointUnionDef {ι:Type u_2} {η:ι → Type u_1} [(i:ι)->TopologicalSpace (η i)] 
{s:Set (Sigma η)} :IsOpen s ↔ ∀ (i : ι), IsOpen (PreIm(Sigma.mk i, s)) :=
isOpen_sigma_iff

lemma disjointUnionDef' {ι:Type u_2} {η:ι → Type u_1} [(i:ι)->TopologicalSpace (η i)] 
{s:Set (Sigma η)} :IsClosed s ↔ ∀ (i : ι), IsClosed (PreIm(Sigma.mk i, s)) :=
isClosed_sigma_iff

lemma sigmaMkIsContinuous {ι:Type u_2} {η:ι→Type u_1} [(i:ι)->TopologicalSpace (η i)] (i : ι) :
Continuous (@Sigma.mk ι η i) :=continuous_sigmaMk

lemma sigmaMkIsEmbedding {ι:Type u_2} {η:ι→Type u_1} [(i:ι)->TopologicalSpace (η i)] (i : ι) :
Embedding (@Sigma.mk ι η i) :=embedding_sigmaMk

lemma disjointUnionUniversalProperty' {ι:Type u_3} {η:ι→Type u_1} {f:Sigma η ->α}
[(i:ι)->TopologicalSpace (η i)] [TopologicalSpace α]:
Continuous f ↔ ∀ (i : ι), Continuous (fun a => f ⟨i, a⟩) :=
continuous_sigma_iff

@[reducible]
instance disjointUnionHausdorffIfAllHasudorff {ι:Type u_2}{η:ι → Type u_1} 
[tsη:(i:ι)->TopologicalSpace (η i)] [hsι:(i:ι)->@HausdorffSpace _ (tsη i)]:
HausdorffSpace (Sigma η) := by
  have p1:(∀ {x y : Sigma η}, x ≠ y → 
  ∃ (u1:neighb x) (u2:neighb y), u1.set ∩ u2.set = ∅) := by
    intro x y hxy
    match x with
    |.mk ιx valx =>  
    match y with
    |.mk ιy valy =>
    by_cases c : ιx = ιy
    · subst c
      have p2:valx ≠ valy := by
        by_contra hc 
        simp_rw [hc] at hxy; simp at hxy
      let p3:=(hsι ιx).property p2
      refine' Exists.elim p3 _
      intro nbx' p3
      refine' Exists.elim p3 _
      intro nby' p3
      let setx:= Im(Sigma.mk ιx,nbx'.set ) 
      let sety:= Im(fun a =>(⟨ιx,a ⟩: Sigma η),nby'.set )
      have px1:IsOpen setx := by
        refine' disjointUnionDef.mpr _
        intro i; by_cases c: i=ιx
        · rw [c]
          have p4:PreIm(Sigma.mk ιx,setx) = nbx'.set := by 
            refine' setEqIff.mpr _
            intro z 
            have mp:z ∈ PreIm(Sigma.mk ιx,setx) -> z ∈ nbx'.set := by
              intro hz; simp at hz; exact hz
            have mpr: z ∈ nbx'.set -> z ∈ PreIm(Sigma.mk ιx,setx)  := by
              intro hz; simp ; exact hz
            exact ⟨mp,mpr ⟩ 
          rw [p4]; exact nbx'.property.right
        · have p4:(PreIm(Sigma.mk i,setx)) = ∅  := by
            by_contra hc
            replace hc:=setNonemptyIff.mpr hc
            simp only [Set.Nonempty] at hc
            refine' Exists.elim hc _
            intro j hj; simp at hj
            refine' Exists.elim hj _
            intro _ hj
            exact c hj.right.left.symm
          rw [p4]; exact emptyIsOpen
      have py1:IsOpen sety := by
        refine' disjointUnionDef.mpr _
        intro i; by_cases c: i=ιx
        · rw [c]
          have p4:PreIm(Sigma.mk ιx,sety) = nby'.set := by 
            refine' setEqIff.mpr _
            intro z 
            have mp:z ∈ PreIm(Sigma.mk ιx,sety) -> z ∈ nby'.set := by
              intro hz; simp at hz; exact hz
            have mpr: z ∈ nby'.set -> z ∈ PreIm(Sigma.mk ιx,sety)  := by
              intro hz; simp ; exact hz
            exact ⟨mp,mpr ⟩ 
          rw [p4]; exact nby'.property.right
        · have p4:(PreIm(Sigma.mk i,sety)) = ∅  := by
            by_contra hc
            replace hc:=setNonemptyIff.mpr hc
            refine' Exists.elim hc _
            intro j hj; simp at hj
            refine' Exists.elim hj _
            intro _ hj
            exact c hj.right.left.symm
          rw [p4]; exact emptyIsOpen
      have px2:⟨ιx,valx ⟩ ∈setx := by
        simp; exact nbx'.property.left
      have py2:⟨ιx,valy ⟩ ∈sety := by
        simp; exact nby'.property.left
      refine' ⟨⟨_,px2,px1⟩,⟨_,py2,py1⟩,_⟩ 
      simp; by_contra hc
      replace hc:=setNonemptyIff.mpr hc
      refine' Exists.elim hc _
      intro z hz; simp at hz
      refine' Exists.elim hz.left _
      intro x' hx'
      refine' Exists.elim hz.right _
      intro y' hy'
      have p4:x'=y' := by
        match z with
        |.mk ιz valz =>
        let p5:=hx'.right; simp at p5
        let p6:=hy'.right; simp at p6
        exact  heq_iff_eq.mp (HEq.trans p5.right p6.right.symm)
      replace p4:(nbx'.set ∩ nby'.set).Nonempty
        :=⟨_,mem_inter hx'.left (p4.symm ▸ hy'.left)⟩ 
      exact (setNonemptyIff.mp p4) p3
    · have p2: (Im(Sigma.mk ιx,univ ):Set ( Sigma η)) ∩ (Im(Sigma.mk ιy,univ )) =∅  := by
        by_contra hc
        replace hc:=setNonemptyIff.mpr hc
        refine' Exists.elim hc _
        intro z hz; simp at hz
        exact c (hz.left ▸ hz.right)
      exact ⟨⟨Im(Sigma.mk ιx,univ ),by simp,
        (OpenEmbedding.open_iff_image_open (openEmbedding_sigmaMk)).mp univIsOpen⟩,
        ⟨Im(Sigma.mk ιy,univ ),by simp,
        (OpenEmbedding.open_iff_image_open (openEmbedding_sigmaMk)).mp univIsOpen⟩,p2⟩ 
  exact ⟨p1⟩ 

@[reducible]
instance disjointUnionFstCountableIfAllFstCountable {N:ℕ}{η:Fin N → Type u_1} 
[tsη:(n:Fin N)->TopologicalSpace (η n)] [fstη:(n:Fin N)->@fstCountable _ (tsη n)]:
fstCountable (Sigma η) := by 
  have p1: (∀ x, ∃ nbB:neighbBasis x, 
  (@neighbBasis.neighbs _ (@instTopologicalSpaceSigma _ _ tsη) _ nbB).atMostCountable)  := by
    intro x 
    match x with
    |.mk ιx valx =>
    let f:neighb valx -> neighb ⟨ιx,valx⟩  :=
      fun nb => 
      ⟨Im(Sigma.mk ιx,nb.set), by simp; exact nb.property.left,
        (OpenEmbedding.open_iff_image_open (openEmbedding_sigmaMk)).mp nb.property.right⟩ 
    let nbB:neighbBasis (⟨ιx,valx ⟩:Sigma η)  := {
      neighbs := Im(f, (choose ( (fstη ιx).property valx)).neighbs) 
      exists_contained := by
        intro nb_given
        have p2: valx ∈ (PreIm(Sigma.mk ιx,nb_given.set)) := by 
          simp;exact nb_given.property.left
        refine' Exists.elim ((choose ( (fstη ιx).property valx)).exists_contained 
          ⟨_,p2,(continuousDef.mp (sigmaMkIsContinuous ιx) nb_given.property.right) ⟩ ) _
        intro nb' hnb'; refine' ⟨f nb',by simp only [mem_image]; refine' ⟨_,hnb'.left,rfl ⟩ ,_⟩ 
        refine' setSubsetIff.mpr _
        intro y hy; simp at hy
        refine' Exists.elim hy _
        intro y' hy'
        let p3:=setSubsetIff.mp hnb'.right _ hy'.left
        simp at p3; rw [hy'.right.symm]; exact p3}
    refine' ⟨nbB,imageOfCountable _ (choose_spec ( (fstη ιx).property valx))⟩ 
  exact ⟨p1⟩ 

end  PointSetTopology
  
namespace Set  

universe u_1 u_2
variable {α:Type u_1} {β:Type u_2}

@[simp]
def saturated (s:Set α) (f:α->β):Prop := 
s = PreIm(f,Im(f,s))

end Set
    
namespace PointSetTopology

open FUNCTION SET Set LIST FINSET Classical NAT COUNTABLE 

universe u_1 u_2 u_3

variable {α: Type u_1} {β :Type u_2}

lemma saturatedIff {f:α->β} {s:Set α}: s.saturated f ↔ ∀{x x':α},x∈s -> f x = f x' -> x'∈s := by
  have mp:s.saturated f -> ∀{x x':α},x∈s -> f x = f x' -> x'∈s := by
    intro h x x' hx hx'
    simp at h; rw [h]; simp
    exact ⟨_,hx,hx' ⟩ 
  have mpr : (∀{x x':α},x∈s -> f x = f x' -> x'∈s )-> (s.saturated f) := by
    intro h; simp only [saturated]
    refine' setEqIff.mpr _
    intro x
    have mp: x∈ s -> x ∈ PreIm(f,Im(f,s)) := by
      intro h2; simp
      exact ⟨_,h2,rfl ⟩ 
    have mpr: x ∈ PreIm(f,Im(f,s)) -> x∈ s := by
      intro h2; 
      refine' Exists.elim h2 _
      intro x' hx'
      exact h hx'.left hx'.right
    exact ⟨mp,mpr ⟩ 
  exact ⟨mp,mpr⟩ 

lemma quotientMkIsContinuous [inst:TopologicalSpace α] [Setoid α] :
@Continuous _ _ inst _  Quotient.mk' := continuous_quotient_mk'
    
lemma quotientSpaceDef [TopologicalSpace α] [st:Setoid α] {s:Set (Quotient st)}:
IsOpen s ↔ ∃ s':Set α, (s'.saturated Quotient.mk') ∧ (IsOpen s')∧ (s=Im(Quotient.mk',s')):= by
  have mp: IsOpen s -> ∃ s':Set α, (s'.saturated Quotient.mk') ∧ (IsOpen s') ∧ (s=Im(Quotient.mk',s')) := by
    intro h; 
    have p1:saturated (PreIm(Quotient.mk',s)) Quotient.mk' := by
      refine' saturatedIff.mpr _
      intro x x' hx hx'; simp; simp at hx
      rw [hx'.symm]; exact hx
    refine' ⟨PreIm(Quotient.mk',s),p1,continuousDef.mp quotientMkIsContinuous h,setEqIff.mpr _ ⟩ 
    intro z
    have mp: z ∈ s -> z ∈ Im(Quotient.mk',PreIm(Quotient.mk',s)) := by
      intro h2; simp 
      refine' ⟨z.out,by simp [Quotient.mk']; exact h2,by simp [Quotient.mk'] ⟩ 
    have mpr:z ∈ Im(Quotient.mk',PreIm(Quotient.mk',s)) ->z∈ s := by
      intro h2; simp at h2
      refine' Exists.elim h2 _
      intro z' hz'; rw [hz'.right.symm]; exact hz'.left
    exact ⟨mp,mpr ⟩ 
  have mpr: (∃ s':Set α, (s'.saturated Quotient.mk') ∧ (IsOpen s')∧ s=Im(Quotient.mk',s')) -> IsOpen s := by
    intro h; refine' Exists.elim h _ 
    intro s' hs'
    let p1:=hs'.left; simp at p1; let p2:=hs'.right.left
    rw [hs'.right.right]; rw [p1] at p2
    exact p2
  exact ⟨mp,mpr⟩ 

lemma quotientSpaceDef' [TopologicalSpace α] [st:Setoid α] {s:Set (Quotient st)}:
IsClosed s ↔ ∃ s':Set α, (s'.saturated Quotient.mk') ∧ (IsClosed s')∧ (s=Im(Quotient.mk',s')):= by
  have mp: IsClosed s -> 
  ∃ s':Set α, (s'.saturated Quotient.mk') ∧ (IsClosed s') ∧ (s=Im(Quotient.mk',s')) := by
    intro h; replace h:=quotientSpaceDef.mp (closedComplIsOpen h)
    refine' Exists.elim h _
    intro s' hs'
    have p1:(s'ᶜ).saturated Quotient.mk' := by
      refine' saturatedIff.mpr _
      intro x x' hx hx'; simp; simp at hx
      by_contra hc
      exact hx (saturatedIff.mp hs'.left hc hx'.symm)
    refine' ⟨_,p1,openComplIsClosed hs'.right.left,_ ⟩ 
    let p2:=congrArg compl hs'.right.right; simp at p2
    rw [p2]; refine' setEqIff.mpr _
    intro z 
    have mp: z ∈ (Im(Quotient.mk',s'))ᶜ -> z ∈ Im(Quotient.mk',s'ᶜ) := by
      intro h2;simp; refine' ⟨z.out,_, by simp [Quotient.mk'] ⟩ 
      by_contra hc
      have p3:z ∈ (Im(Quotient.mk',s')) := by
        have p4: Quotient.mk' z.out = z := by simp [Quotient.mk']
        rw [p4.symm]; simp only [mem_image]; exact ⟨_,hc,by simp ⟩ 
      exact h2 p3
    have mpr: z ∈ Im(Quotient.mk',s'ᶜ) ->  z ∈ (Im(Quotient.mk',s'))ᶜ := by
      intro h2; simp at h2
      refine' Exists.elim h2 _
      intro y hy; rw [hy.right.symm,mem_compl_iff]
      by_contra hc; simp only [mem_image] at hc
      refine' Exists.elim hc _
      intro x hx
      let p3:= saturatedIff.mp (hs'.left) hx.left hx.right
      exact hy.left p3
    exact ⟨mp,mpr⟩ 
  have mpr: (∃ s':Set α, (s'.saturated Quotient.mk') ∧ (IsClosed s')∧ s=Im(Quotient.mk',s')) 
  -> IsClosed s := by
    intro h1
    refine' Exists.elim h1 _
    intro s' hs'
    have p1: (Im(Quotient.mk',s'))ᶜ = Im(Quotient.mk',s'ᶜ) := by
      refine' setEqIff.mpr _
      intro z 
      have mp: z ∈ (Im(Quotient.mk',s'))ᶜ -> z ∈ Im(Quotient.mk',s'ᶜ) := by
        intro h2;simp; refine' ⟨z.out,_, by simp [Quotient.mk'] ⟩ 
        by_contra hc
        have p3:z ∈ (Im(Quotient.mk',s')) := by
          have p4: Quotient.mk' z.out = z := by simp [Quotient.mk']
          rw [p4.symm]; simp only [mem_image]; exact ⟨_,hc,by simp ⟩ 
        exact h2 p3
      have mpr: z ∈ Im(Quotient.mk',s'ᶜ) ->  z ∈ (Im(Quotient.mk',s'))ᶜ := by
        intro h2; simp at h2
        refine' Exists.elim h2 _
        intro y hy; rw [hy.right.symm,mem_compl_iff]
        by_contra hc; simp only [mem_image] at hc
        refine' Exists.elim hc _
        intro x hx
        let p3:= saturatedIff.mp (hs'.left) hx.left hx.right
        exact hy.left p3
      exact ⟨mp,mpr⟩ 
    have p2:(sᶜ)ᶜ = s := by rw [setComplCompl]
    rw [p2.symm]; refine' openComplIsClosed _
    rw [hs'.right.right,p1]; 
    refine' quotientSpaceDef.mpr ⟨s'ᶜ,saturatedIff.mpr _,closedComplIsOpen hs'.right.left,rfl ⟩ 
    intro x x' hx hx'; by_contra hc; simp at hc
    replace hc :=saturatedIff.mp hs'.left hc hx'.symm
    exact hx hc
  exact ⟨mp,mpr⟩ 

lemma quotientSpaceUniversalProperty [TopologicalSpace α] [TopologicalSpace β]
{st:Setoid α} {f:α->β} (h1:Continuous f) (h2:∀ (a b : α), a ≈ b → f a = f b):
∃! f' : Quotient st ->β, Continuous f' ∧ f'∘ (@Quotient.mk _ st) =f := by
  simp [ExistsUnique] ; 
  refine' ⟨_,⟨Continuous.quotient_lift h1 h2,Quotient.lift_comp_mk _ h2 ⟩,_⟩   
  intro y _ h2y; refine' funcEqIff.mpr _
  intro x;  
  have p1:⟦x.out⟧ = x := Quotient.out_eq _
  rw [p1.symm]
  exact congrFun h2y x.out

lemma saturatedOpenToOpenImpliesQuotient {q:α->β}[Nonempty α] [TopologicalSpace α] [TopologicalSpace β] 
(h1:Continuous q)(h2:Function.Surjective q)(h3:∀{s:Set α},(s.saturated q)∧IsOpen s -> IsOpen (Im(q,s)) )
:@Homeomorph β _ _ (@instTopologicalSpaceQuotient _ 
⟨fun x1 x2=> q x1 = q x2,⟨by simp,fun h=>h.symm,fun h1 h2=> h1▸ h2 ⟩⟩ _)  := by
  let st:Setoid α :=⟨fun x1 x2=> q x1 = q x2,⟨by simp,fun h=>h.symm,fun h1 h2=> h1▸ h2 ⟩⟩
  have p1: ∀ (a b : α), a ≈ b → q a = q b := by
    intro a b hab; exact hab 
  exact {
    toEquiv:={ 
      toFun:=(@Quotient.mk' _ st)∘ (Function.invFun q)
      invFun:=Quotient.lift _ p1
      left_inv := by
        simp only [Function.LeftInverse]
        intro b ; simp
        exact congrFun (funcSurjRightInvComp h2) b
      right_inv := by
        simp only [Function.RightInverse,Function.LeftInverse]
        intro x; simp
        have p2:∀{a:α}{b:β},q a = b -> (Quotient.mk' ((Function.invFun q) b))
        = Quotient.mk' a := by
          intro a b H
          have p3: q ((Function.invFun q) b) = b := 
            congrFun (funcSurjRightInvComp h2) b
          simp  [Quotient.mk',HasEquiv.Equiv]; 
          exact  p3.trans H.symm
        have p3:q x.out = Quotient.lift _ p1 x := by
          have p4:⟦x.out⟧ = x := Quotient.out_eq _
          calc 
            q x.out = Quotient.lift _ p1 ⟦x.out⟧  := by rw [Quotient.lift_mk]
            _ = Quotient.lift _ p1 x := by rw [p4]
        rw [p2 p3]; exact Quotient.out_eq _}
    continuous_toFun:= by
      simp
      refine' continuousDef.mpr _
      intro s hs; replace hs:=quotientSpaceDef.mp hs
      refine' Exists.elim hs _
      intro s' hs'
      have p2:s'.saturated q := by
        refine' saturatedIff.mpr _
        intro x x' hx hx'
        exact saturatedIff.mp hs'.left hx (by simp [Quotient.mk'];exact hx')
      replace p2:=h3 ⟨p2,hs'.right.left⟩ 
      have p3: (PreIm((Quotient.mk' ∘ Function.invFun q),s)) =  Im(q,s') := by
        refine' setEqIff.mpr _
        intro x
        let p4:=congrFun (funcSurjRightInvComp h2) x; simp at p4
        have mp: x ∈ PreIm((Quotient.mk' ∘ Function.invFun q),s) -> x ∈ Im(q,s') := by
          intro H;rw [hs'.right.right] at H; simp at H; 
          rw [p4] at H; simp ; exact H
        have mpr: x ∈ Im(q,s') -> x ∈ PreIm((Quotient.mk' ∘ Function.invFun q),s) := by
          intro H; rw [hs'.right.right];simp
          rw [p4]; simp at H; exact H
        exact ⟨mp,mpr⟩ 
      rw [p3];exact p2
    continuous_invFun := Continuous.quotient_lift h1 p1 }
    
lemma saturatedClosedToClosedImpliesQuotient {q:α->β}[Nonempty α] [TopologicalSpace α] [TopologicalSpace β] 
(h1:Continuous q)(h2:Function.Surjective q)(h3:∀{s:Set α},(s.saturated q)∧ IsClosed s -> IsClosed (Im(q,s)) )
:@Homeomorph β _ _ (@instTopologicalSpaceQuotient _ 
⟨fun x1 x2=> q x1 = q x2,⟨by simp,fun h=>h.symm,fun h1 h2=> h1▸ h2 ⟩⟩ _)  := by
  have p1: ∀{s:Set α},(s.saturated q)∧ IsOpen s -> IsOpen (Im(q,s)) := by
    intro s hs
    have p2:(sᶜ).saturated q := by
      refine' saturatedIff.mpr _
      intro x x' hx hx'
      by_contra hc ; simp at hc
      exact hx (saturatedIff.mp hs.left hc hx'.symm)
    have p3:(Im(q,s))ᶜ  = Im(q,sᶜ) := by
      refine' setEqIff.mpr _
      intro x 
      have mp:x∈ (Im(q,s))ᶜ -> x ∈ Im(q,sᶜ) := by
        intro H ;  simp only [mem_image]
        refine' ⟨(Function.invFun q) x, _ ,congrFun (funcSurjRightInvComp h2) x⟩ 
        by_contra hc; simp at hc
        have p4:x∈ (Im(q,s)) := by 
          simp only [mem_image]
          exact ⟨_,hc,congrFun (funcSurjRightInvComp h2) x ⟩ 
        exact H p4
      have mpr:  x ∈ Im(q,sᶜ) -> x∈ (Im(q,s))ᶜ := by
        intro H; simp only [mem_image] at H
        refine' Exists.elim H _
        intro y hy; by_contra hc; simp at hc
        refine' Exists.elim hc _ 
        intro y' hy' ; rw [hy.right.symm] at hy'
        exact hy.left (saturatedIff.mp hs.left hy'.left hy'.right)
      exact ⟨mp,mpr⟩ 
    replace p2:=closedComplIsOpen (h3 ⟨p2,openComplIsClosed hs.right⟩ )
    rw [p3.symm] at p2; simp at p2; exact p2
  exact saturatedOpenToOpenImpliesQuotient h1 h2 p1










  


















