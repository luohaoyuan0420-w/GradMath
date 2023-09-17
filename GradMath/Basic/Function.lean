import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Lattice

namespace FUNCTION

universe u_1 u_2 u_3

lemma cirIsComp  {α:Sort u_1} {β:Sort u_2} {γ:Sort u_3}
{f : β → γ} {g : α → β} {a : α} : (f ∘ g) a = f (g a) := 
Function.comp_apply

lemma funcEqIff {α : Sort u_1} {β : α → Sort u_2} {f1 f2:∀a, β a}:
f1 = f2 ↔ ∀ a, f1 a = f2 a := Function.funext_iff

lemma funcNeIff {α : Sort u_1} {β : α → Sort u_2} {f1 f2:∀a, β a}:
f1 ≠ f2 ↔ ∃ a, f1 a ≠ f2 a := Function.ne_iff

lemma funcInjNeq {α : Sort u_1} {β : Sort u_2} {f : α → β} 
(hf : Function.Injective f) {a1 a2 : α}: a1≠a2 -> f a1 ≠ f a2 
:=Function.Injective.ne hf

lemma funcSurjForall {α : Sort u_1} {β : Sort u_2} {f : α → β} 
(hf : Function.Surjective f) {p : β → Prop}:(∀(x : α), p (f x))-> (∀ (y : β), p y)
:=(@Function.Surjective.forall _ _ _ hf p).mpr 

lemma funcInjInjComp {α:Sort u_1} {β:Sort u_2} {γ:Sort u_3} {f1:β->γ}{f2:α→β} 
(hf1 : Function.Injective f1) (hf2 : Function.Injective f2):
Function.Injective (f1∘f2):=(Function.Injective.of_comp_iff hf1 f2).mpr hf2

lemma funcSurjSurjComp {α:Sort u_1} {β:Sort u_2} {γ:Sort u_3} {f1:β->γ}{f2:α→β}
(hf1 : Function.Surjective f1) (hf2 : Function.Surjective f2):
Function.Surjective (f1∘f2):=(Function.Surjective.of_comp_iff f1 hf2).mpr hf1

lemma funcBijExistsUnique {α : Sort u_1} {β : Sort u_2} {f : α → β} 
(hf :Function.Bijective f) (b : β) : ∃! (a : α), f a = b := 
Function.Bijective.existsUnique hf b

lemma funcLeftInvInjComp {α : Sort u_1} {β : Sort u_2} [Nonempty α] {f : α → β} 
(hf :Function.Injective f) :Function.invFun f ∘ f = id := 
Function.invFun_comp hf

lemma funcSurjRightInvComp {α : Sort u_1} {β : Sort u_2} [Nonempty α] {f : α → β}
(hf: Function.Surjective f):  f ∘ (Function.invFun f) = id := by 
  let p1:=Function.rightInverse_invFun hf
  simp [Function.RightInverse,Function.LeftInverse] at p1
  exact funcEqIff.mpr p1

lemma funcInjInvSurj {α : Sort u_1} {β : Sort u_2} [Nonempty α] {f : α → β} 
(hf : Function.Injective f) :Function.Surjective (Function.invFun f) := 
Function.invFun_surjective hf

lemma funcBijInvUnique {α : Sort u_1} {β : Sort u_2} [Nonempty α] {f:α→β}{g:β->α} 
(hf: Function.Bijective f) (hg:(f∘g=id)∨(g∘f=id)) :(Function.invFun f)=g := by 
  cases' hg with hg1 hg2
  · apply funcEqIff.mpr
    intro x ; let p1:=hf.left
    rw [Function.Injective] at p1
    apply p1;
    let p2:=@cirIsComp _ _ _ f g x
    let p3:=@cirIsComp _ _ _ f (Function.invFun f) x
    rw [funcSurjRightInvComp hf.right] at p3 ;rw [p3.symm,p2.symm]
    rw [hg1]
  · apply funcEqIff.mpr
    let p1:=@funcSurjForall _ _ _ hf.right (fun a=>(Function.invFun f a = g a))
    apply p1; intro x 
    let p2:=@cirIsComp _ _ _ g f x
    rw [hg2] at p2 ; rw [p2.symm]
    let p3:=@cirIsComp _ _ _ (Function.invFun f) f x
    rw [funcLeftInvInjComp hf.left] at p3 ; rw [p3.symm]

def Id1' {α:Type u_1} {s1 s2 :Set α} (h:s1⊆s2) :(Subtype s1)->(Subtype s2):=
  fun x => ⟨x.val, Set.mem_of_subset_of_mem h x.property⟩ 

def Id2' {α:Type u_1} {s1 s2 :Set α} (h:∀{x},x∈s1 ->x∈s2): (Subtype s1)->(Subtype s2):=
  fun x=> ⟨x.val, h x.property⟩ 

notation :111 "Im(" f:110 "," s:110 ")" => Set.image f s
notation :111 "PreIm(" f:110 "," s:110 ")" => Set.preimage f s

lemma preImNonemtpyMpr {α:Type u_1} {β:Type u_2} {s :Set α} (f:α->β) (h:s.Nonempty)
: Im(f,s).Nonempty := Set.Nonempty.image f h

lemma imSUnion {α:Type u_1} {β:Type u_2} {s :Set (Set α)} {f:α->β}:
(Im(f,⋃₀ s)) = ⋃₀ (Im(fun x => Im(f,x), s))   := by 
  refine' Set.ext_iff.mpr _
  intro y
  have mp : y∈(Im(f,⋃₀ s)) -> y∈⋃₀ (Im(fun x => Im(f,x),s)) := by
    intro h1
    simp at h1; simp
    refine' Exists.elim h1 _
    intro x h2
    refine' Exists.elim h2.left _
    intro si h3
    exact ⟨_,h3.left,_,h3.right,h2.right ⟩ 
  have mpr : y∈⋃₀ (Im(fun x => Im(f,x),s)) -> y∈(Im(f,⋃₀ s)) := by
    intro h1
    simp at h1; simp
    refine' Exists.elim h1 _
    intro si h2
    refine' Exists.elim h2.right _
    intro x h3
    exact ⟨x,⟨_,h2.left,h3.left ⟩ ,h3.right⟩ 
  exact ⟨mp,mpr⟩ 

lemma imUnion {α : Type u_1} {β : Type u_2} {f : α → β} {s t : Set α} :
Im(f,(s∪t)) = (Im(f,s))∪(Im(f,t)) :=@Set.image_union _ _ f s t 

lemma preImSUnion  {α:Type u_1} {β:Type u_2} {s :Set (Set β)} (f:α->β):
(PreIm(f,⋃₀ s)) = ⋃₀ (Im(fun x => PreIm(f,x), s)) := by 
  refine' Set.ext_iff.mpr _
  intro x
  have mp:  x ∈ (PreIm(f,⋃₀ s)) ->x ∈ ⋃₀  (Im(fun x => PreIm(f,x),s)) := by
    intro h1
    simp at h1; simp
    exact h1
  have mpr:x ∈ ⋃₀ (Im(fun x => PreIm(f,x),s)) -> x ∈ (PreIm(f,⋃₀ s)) := by
    intro h1
    simp at h1; simp
    exact h1
  exact ⟨mp,mpr⟩ 

lemma preImUnion {α : Type u_1} {β : Type u_2} (f : α → β) (s t : Set β) :
PreIm(f,(s∪t)) = PreIm(f,s) ∪ PreIm(f,t):=@Set.preimage_union _ _ f s t

lemma preImSInter  {α:Type u_1} {β:Type u_2} {s :Set (Set β)} (f:α->β):
PreIm(f,⋂₀ s) = ⋂₀ (Im(fun x => PreIm(f,x), s)) := by 
  refine' Set.ext_iff.mpr _
  intro x
  have mp:  x ∈ (PreIm(f,⋂₀ s)) ->x ∈ ⋂₀ (Im(fun x => PreIm(f,x),s)) := by
    intro h1
    simp at h1; simp
    exact h1
  have mpr:x ∈ ⋂₀ (Im(fun x => PreIm(f,x),s)) -> x ∈ (PreIm(f,⋂₀ s)) := by
    intro h1
    simp at h1; simp
    exact h1
  exact ⟨mp,mpr⟩ 

lemma preImInter {α : Type u_1} {β : Type u_2} {f : α → β} {s t : Set β} :
PreIm(f,(s∩t)) = PreIm(f,s)∩PreIm(f,t) :=@Set.preimage_inter _ _ f s t

lemma imSubset {α : Type u_1}{β : Type u_2}{s t:Set α}(f:α→β)(h:s⊆t):
Im(f,s) ⊆ Im(f,t) := @Set.image_subset _ _ _ _ f h

lemma preImSubset {α : Type u_1}{β : Type u_2}{s t:Set β}(f:α→β)(h:s⊆t):
PreIm(f,s) ⊆ PreIm(f,t) := by
  rw [Set.subset_def]
  intro x h1
  simp at h1; simp 
  rw [Set.subset_def] at h
  exact h _ h1

lemma preImCompl {α : Type u_1}{β : Type u_2}{s:Set β}(f:α→β):
PreIm(f,sᶜ) = (PreIm(f,s))ᶜ := by simp

lemma preImComp {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β} {g : β → γ} {s : Set γ} :
PreIm((g∘f),  s) =PreIm( f , PreIm(g, s)) :=Set.preimage_comp

lemma imComp {α:Type u_1}{β:Type u_2}{γ:Type u_3}{f:β→γ}{g:α→β}{a:Set α} :
Im((f∘g), a) = Im(f, Im(g , a)):= Set.image_comp f g a

end FUNCTION


















