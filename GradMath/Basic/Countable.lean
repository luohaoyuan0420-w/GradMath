import GradMath.Basic.Function
import GradMath.Basic.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Zify

noncomputable section

open FUNCTION Function SET LIST FinProd
namespace COUNTABLE

def oneDimToTwo.f: ℕ × ℕ -> ℕ := fun x => ((x.1+x.2)*(x.1+x.2+1))/2 + x.1

lemma oneDimToTwo.fInj :Injective f := by
  simp [Injective,oneDimToTwo.f]
  intro a b a' b' h
  by_cases c1 : (a+b)=(a'+b')
  case pos =>
    rw [c1, Nat.add_comm _ a, Nat.add_comm _ a'] at h; 
    replace h:=congrArg (.-((a' + b') * (a' + b' + 1) / 2)) h
    simp at h; rw [h, Nat.add_comm _ b, Nat.add_comm _ b'] at c1; 
    replace c1:=congrArg (.-a') c1; simp at c1
    exact ⟨h,c1⟩ 
  case neg =>
    have p2 {x y:Nat}: x*2<y*2 -> x<y  := by
      intro h1
      by_contra hc
      push_neg at hc
      let p2:=Nat.mul_le_mul hc ((by simp):2≤2)
      have p3:= calc
        _ < _ := h1
        _ ≤ _ := p2
      simp at p3
    by_cases c2: (a+b) < (a'+b')
    · let p1:=Nat.succ_le_iff.mpr c2 
      refine' absurd h (p2 _).ne
      rw [Nat.right_distrib _ _ 2, Nat.right_distrib _ _ 2];
      let p3:= Nat.div_two_mul_two_of_even
        (Nat.even_mul_succ_self (a+b))
      let p4:=  Nat.div_two_mul_two_of_even
        (Nat.even_mul_succ_self (a'+b'))
      rw [p3,p4];
      have p5:(a+b)*(a+b+1)+a*2<((a+b).succ)*((a+b+1).succ) := by
        have p6: ((a+b).succ)*((a+b+1).succ)=2*b+2+((a+b)*(a+b+1)+a*2) := by
          zify; ring
        rw [p6];
        have p7: 0 < 2*b+2 := by simp
        replace p7:=Nat.add_lt_add_right p7 ((a+b)*(a+b+1)+a*2)
        rw [zero_add] at p7; exact p7
      calc 
        _ < _ := p5
        _ ≤ (a' + b') * (a' + b' + 1) 
            := Nat.mul_le_mul p1 (Nat.succ_le_succ p1)
        _ ≤ _ := by simp
    · push_neg at c2 c1
      replace c2:= c2.lt_of_ne c1.symm
      let p1:=Nat.succ_le_iff.mpr c2 
      refine' absurd h.symm (p2 _).ne
      rw [Nat.right_distrib _ _ 2, Nat.right_distrib _ _ 2];
      let p3:= Nat.div_two_mul_two_of_even
        (Nat.even_mul_succ_self (a+b))
      let p4:=  Nat.div_two_mul_two_of_even
        (Nat.even_mul_succ_self (a'+b'))
      rw [p3,p4];
      have p5:(a'+b')*(a'+b'+1)+a'*2<((a'+b').succ)*((a'+b'+1).succ) := by
        have p6: ((a'+b').succ)*((a'+b'+1).succ)=2*b'+2+((a'+b')*(a'+b'+1)+a'*2) := by
          zify; ring
        rw [p6];
        have p7: 0 < 2*b'+2 := by simp
        replace p7:=Nat.add_lt_add_right p7 ((a'+b')*(a'+b'+1)+a'*2)
        rw [zero_add] at p7; exact p7
      calc 
        _ < _ := p5
        _ ≤ (a +b) * (a+ b+ 1) 
            := Nat.mul_le_mul p1 (Nat.succ_le_succ p1)
        _ ≤ _ := by simp

lemma existsOneDimToTwo :∃ f:ℕ->ℕ×ℕ , Surjective f := by
  exact ⟨_, funcInjInvSurj oneDimToTwo.fInj⟩ 

universe u_1 u_2
variable {α: Type u_1} {β: Type u_2}

lemma sUnionOfCountable {S: Set (Set α)} (h1:S.atMostCountable)
(h2: ∀{s':Set α}, (s'∈S) -> s'.atMostCountable) : (⋃₀ S).atMostCountable := by 
  simp only [Set.atMostCountable] at h1 h2
  refine' Exists.elim h1 _
  intro f1 hf1
  have p1:∀(n1:Nat), f1 n1 ∈ S := by
    rw [hf1]; simp
  have p2 {s':Set α} (h3:s'∈S):∀(n2:Nat), (Classical.choose (h2 h3) n2)∈(⋃₀ S) := by
    intro n2; 
    let p3:=Classical.choose_spec (h2 h3)
    set f2:=Classical.choose (h2 h3)
    have p4: f2 n2 ∈ s' := by
      rw [p3]; simp; 
    simp at p4
    simp; exact ⟨_,h3,p4⟩ 
  set F:Nat×Nat ->⋃₀ S  := by
    intro x
    let f2:=Classical.choose (h2 (p1 x.1))
    exact ⟨f2 x.2, p2 (p1 x.1) x.2⟩ 
    with HH
  have p3: Surjective F := by
    simp [Surjective]
    intro y s' hs' hy 
    rw [hf1] at hs'; simp at hs'
    refine' Exists.elim hs' _
    intro n1 hs'
    let p4:=Classical.choose_spec (h2 (p1 n1))
    set f2:=Classical.choose (h2 (p1 n1))
    rw [hs'.symm,p4] at hy
    simp only [Set.mem_image] at hy;
    refine' Exists.elim hy _
    intro n2 hy 
    refine' ⟨n1,n2,_⟩ 
    exact hy.right
  refine' Exists.elim existsOneDimToTwo _
  intro G hG
  simp only [Set.atMostCountable]
  refine' ⟨Subtype.val∘F∘G,setEqIff.mpr _⟩ 
  intro z 
  let p4:=funcSurjSurjComp p3 hG
  simp only [Surjective] at p4
  have mp : z ∈ ⋃₀ S ->z ∈ Im((Subtype.val ∘ F ∘ G),Set.univ) := by 
    intro h3
    refine' Exists.elim (p4 ⟨_,h3⟩ )  _
    intro n h4 ; simp only [Set.mem_image]
    rw [← HH]; rw [← HH] at h4
    let p5:=congrArg (Subtype.val) h4
    exact ⟨_,(by simp),p5⟩ 
  have mpr: z ∈ Im((Subtype.val ∘ F ∘ G),Set.univ) -> z ∈ ⋃₀ S:= by
    intro h3; simp only [Set.mem_image] at h3
    refine' Exists.elim h3 _
    intro n h3; rw [← HH] at h3
    set z':= (F∘G) n with HH2
    have p5:z=z'.val := by
      rw [HH2]; exact h3.right.symm
    rw [p5]; exact z'.property
  exact ⟨mp,mpr⟩ 

open Classical
def subsetOfCountable.F {s t:Set α} (h0:s.Nonempty) (h1:s⊆t) (h2:t.atMostCountable):
ℕ -> α:= fun n => 
  let f1:=choose h2
  match n with
  | 0 =>  
    if (f1 0) ∈s 
      then  f1 0
      else choose h0
  | .succ n' => 
    if f1 (.succ n') ∈ s 
      then   f1 (.succ n')
      else  subsetOfCountable.F h0 h1 h2 n'

lemma subsetOfCountable {s t:Set α} (h0:s.Nonempty) (h1:s⊆t) (h2:t.atMostCountable):
(s.atMostCountable) :=by
  simp only [Set.atMostCountable]
  let F:=subsetOfCountable.F h0 h1 h2
  refine' ⟨F, _⟩ 
  simp only [Set.atMostCountable] at h2
  refine' setEqIff.mpr _
  intro y 
  let hg:=choose_spec h2
  have mp: y ∈ s ->y ∈ Im(F,Set.univ) := by
    intro h3; 
    let p1:=setSubsetIff.mp h1 _ h3
    rw [hg] at p1; simp only [Set.mem_image] at p1
    refine' Exists.elim p1 _
    intro n h4
    refine' ⟨n,_⟩ 
    match n with 
    | 0 =>
      simp [subsetOfCountable.F]
      set g:=choose h2
      simp only [h4.right.symm ▸ h3]
      exact h4.right
    | .succ n' =>
      simp [subsetOfCountable.F]
      set g:=choose h2
      simp only [h4.right.symm ▸ h3]
      exact h4.right
  have mpr: y∈Im(F,Set.univ) -> y∈s  := by
    intro h3 
    simp only [Set.mem_image] at h3
    refine' Exists.elim h3 _
    intro n h3
    let rec p2: ∀ n:Nat, subsetOfCountable.F h0 h1 h2 n ∈ s  := by
      intro m
      match m with
      | 0 => 
        simp [subsetOfCountable.F]
        set g:=choose h2
        by_cases c1: g 0 ∈ s
        · simp only [c1,if_true]
        · simp only [c1,if_false]
          exact choose_spec h0
      | .succ m' =>
        simp [subsetOfCountable.F]
        set g:=choose h2
        by_cases c1: g (.succ m') ∈ s
        · simp only [c1,if_true]
        · simp only [c1,if_false]
          exact p2 m'
    rw [h3.right.symm]
    exact p2 n
  exact ⟨mp,mpr⟩ 
          
lemma prodOfCountable {s:Set α} {t:Set β} (hs:s.atMostCountable) (ht:t.atMostCountable)
: (s ×ˢ t).atMostCountable := by 
  simp only [Set.atMostCountable]
  simp only [Set.atMostCountable] at hs ht
  refine' Exists.elim hs _
  intro fs hs
  refine' Exists.elim ht _
  intro ft ht
  let f:ℕ×ℕ -> α×β := fun x => (fs x.1, ft x.2)
  have p1: s ×ˢ t = Im(f,Set.univ) := by
    refine' setEqIff.mpr _
    intro z
    have mp: z ∈ s ×ˢ t -> z ∈ Im(f,Set.univ) := by
      intro h1; simp at h1
      let h1_1:=h1.left; rw [hs] at h1_1
      simp at h1_1
      let h1_2:=h1.right; rw [ht] at h1_2
      simp at h1_2
      refine' Exists.elim h1_1 _
      intro n1 h1_1
      refine' Exists.elim h1_2 _
      intro n2 h1_2
      simp
      have p2:(fs n1, ft n2) = z := by
        rw [h1_1,h1_2]; 
      exact ⟨_,_,p2⟩ 
    have mpr: z ∈ Im(f,Set.univ) -> z ∈ s ×ˢ t := by
      intro h1; simp at h1
      refine' Exists.elim h1 _
      intro n1 h1
      refine' Exists.elim h1 _
      intro n2 h1
      simp
      have p2: z.1=fs n1 := by
        rw [h1.symm]
      have p3: z.2=ft n2 := by
        rw [h1.symm]
      rw [p2,p3,hs,ht]; simp
    exact ⟨mp,mpr⟩ 
  refine' Exists.elim existsOneDimToTwo _
  intro g hg; simp [Surjective] at hg
  refine' ⟨f∘g, setEqIff.mpr _ ⟩ 
  intro z
  have mp: z ∈ s ×ˢ t -> z ∈ Im((f ∘ g),Set.univ) := by
    intro h1
    rw [p1] at h1
    simp at h1
    refine' Exists.elim h1 _ 
    intro n1 h1
    refine' Exists.elim h1 _
    intro n2 h1
    rw [h1.symm]; simp
    refine' Exists.elim (hg n1 n2) _
    intro n hn
    refine' ⟨n,_⟩ 
    rw [hn]; simp
  have mpr: z ∈ Im((f ∘ g),Set.univ) -> z ∈ s ×ˢ t := by
    intro h1
    simp at h1; simp
    refine' Exists.elim h1 _
    intro n hn
    rw [hn.symm]; simp
    rw [hs,ht]; simp
  exact ⟨mp,mpr⟩ 

lemma imageOfCountable {s: Set α} (f:α->β) (h:s.atMostCountable)
: Im(f,s).atMostCountable := by
  simp [Set.atMostCountable]; simp [Set.atMostCountable] at h
  refine' Exists.elim h _
  intro g hg
  refine' ⟨f∘g,setEqIff.mpr _⟩ 
  intro z
  have mp: z ∈ Im(f,s) ->z ∈ Set.range (f∘g) := by
    intro h1
    simp at h1; simp
    refine' Exists.elim h1 _
    intro x hx
    rw [hg] at hx; simp at hx
    refine' Exists.elim hx.left _
    intro n hn
    exact ⟨_,hn.symm ▸ hx.right⟩ 
  have mpr: z ∈ Set.range (f∘g) ->  z ∈ Im(f,s) := by
    intro h1
    simp; simp at h1
    refine' Exists.elim  h1 _
    intro n hn; rw [hg]
    exact ⟨g n,(by simp),hn⟩ 
  exact ⟨mp,mpr⟩ 

lemma finsetIsCountable {s:Finset α} (h:s.Nonempty): s.toSet.atMostCountable := by
  simp only [Set.atMostCountable]
  simp [Finset.Nonempty] at h
  let hx :=choose_spec h
  set x:=choose h
  let l:=s.toList
  let f:= fun (n:Nat) =>
    if c1:n<l.length
      then l[n]
      else x
  refine' ⟨f,setEqIff.mpr _ ⟩ 
  intro z 
  have mp: z ∈ ↑s -> z ∈ Im(f,Set.univ) := by
    intro h1; 
    have p1: z∈l := by simp; exact h1
    refine' Exists.elim (listMemIff.mp p1) _
    intro n hn1
    refine' Exists.elim hn1 _
    intro hn1 hn2; simp at hn1
    refine' ⟨n,_ ⟩ ; simp [hn1]
    exact hn2
  have mpr: z ∈ Im(f,Set.univ) -> z ∈ ↑s := by
    intro h1; simp only [Set.mem_image] at h1
    refine' Exists.elim h1 _
    intro n hn; 
    by_cases c1: n<s.card
    case pos =>
      simp [c1] at hn
      rw [hn.symm]; 
      have p1:n<s.toList.length := by simp [c1]
      let p2:=listGetIsMem p1; simp at p2
      exact p2
    case neg => 
      simp [c1] at hn; rw [hn.symm]
      exact hx
  exact ⟨mp,mpr⟩ 
 
lemma NIsCountable : ( Set.univ:Set ℕ).atMostCountable := by
  simp [Set.atMostCountable]
  refine' ⟨(.),_ ⟩ 
  simp

lemma ZIsCountable :(Set.univ: Set ℤ).atMostCountable:= by
  let s1:=[0,1].toFinset
  let p1:= finsetIsCountable ((by simp) :s1.Nonempty)
  let p2:=prodOfCountable p1 NIsCountable
  let f:ℕ × ℕ -> ℤ :=   
    fun x => if x.1 =0 then x.2 else (-x.2:Int)
  have p3:Im(f,(↑s1 ×ˢ Set.univ)) = Set.univ := by
    refine' setEqIff.mpr _
    intro z
    have mp: z ∈ Im(f,(↑s1 ×ˢ Set.univ)) -> z ∈ Set.univ := by simp
    have mpr: z ∈ Set.univ->z ∈ Im(f,(↑s1 ×ˢ Set.univ))  := by
      intro _; simp
      match z with
      | .ofNat n => exact Or.inl ⟨n,(by simp)⟩ 
      | .negSucc n => 
        refine' Or.inr ⟨n.succ,_ ⟩ ;abel
    exact ⟨mp,mpr⟩ 
  exact p3 ▸ imageOfCountable f p2

lemma QIsCountable : (Set.univ: Set ℚ).atMostCountable:= by
  let f : ℤ×ℕ -> ℚ := 
    fun x =>
      if h1:0≠x.2
        then
          @dite _ ((Int.natAbs x.1).coprime x.2) (dec _)
            (fun h2=>⟨x.1,x.2,h1.symm,h2⟩ ) (fun _ => 0)
        else 0
  let p2:((Set.univ:Set ℤ)×ˢ(Set.univ:Set ℕ)).atMostCountable
    :=prodOfCountable ZIsCountable NIsCountable
  have p3:((Set.univ:Set ℤ)×ˢ(Set.univ:Set ℕ))=Set.univ := by simp
  have p1: Im(f,Set.univ) = Set.univ := by
    refine' setEqIff.mpr _
    intro q
    have mp: q ∈ Im(f,Set.univ) -> q ∈ Set.univ := by simp
    have mpr: q ∈ Set.univ -> q ∈ Im(f,Set.univ) := by 
      intro _; simp only [Set.mem_image]
      refine' ⟨(q.num,q.den),(by simp),_ ⟩ 
      simp   [q.den_nz.symm]
      simp [dite]
      set A:= (Nat.instDecidableCoprime_1 (Int.natAbs q.num) q.den)
      match A with
      |isTrue p => simp
      |isFalse p => 
        exact absurd q.reduced p
    exact ⟨mp,mpr⟩ 
  refine' Eq.subst p1 (imageOfCountable f _)
  rw [p3.symm]; exact p2

lemma subtypeIsCountable {s:Set α} (h:s.atMostCountable):
(Set.univ: Set (Subtype s)).atMostCountable := by 
  let f:(Subtype s) -> α := fun x => x.val
  have p1: Injective f := by
    simp [Injective]
  have p2:s.Nonempty := by
    simp [Set.Nonempty]; 
    simp only [Set.atMostCountable] at h
    refine' Exists.elim h _
    intro f hf
    rw [hf]; simp
    exact ⟨f 0,0,rfl⟩ 
  have p3: (Nonempty (Subtype s)) := by
    simp
    exact p2
  let g:=invFun f
  have p4: Im(g,s) = Set.univ := by
    refine' setEqIff.mpr _
    intro x
    have mp:x ∈ Im(g,s) -> x ∈ Set.univ := by
      simp
    have mpr: x∈Set.univ ->x ∈ Im(g,s) := by
      intro _; simp
      refine' ⟨x.val, _⟩ 
      let p4:=congrFun (funcLeftInvInjComp p1) x
      simp at p4; exact ⟨x.property,p4⟩ 
    exact ⟨mp,mpr⟩ 
  rw [p4.symm]; exact imageOfCountable g h

lemma finProdOfCountable {N:ℕ}{η:Fin N -> Type u_1} [inst:Nonempty (Fin N)]
(setη:(n:Fin N) -> (Set (η n)))(h:∀(n:Fin N),(setη n).atMostCountable):
{l:(n:Fin N) ->η n| ∀m:Fin N, l m ∈ setη m}.atMostCountable 
:= by
  set NN:=N with HH
  replace HH:=HH.symm
  match NN with
  | 0 => 
    match inst with
    |.intro n =>
      match n with
      |.mk _ p1 =>
        simp at p1
  | 1 =>
    subst HH
    have p1:∀{m:Fin 1}, 0=m := by 
      intro m; simp
    let p2 {m}:η 0 =η m := by
      rw [p1]
    let f: η 0 ->(n:Fin 1) -> η n := 
      fun s =>fun n => cast (@p2 n) s
    have p3:{l:(n:Fin 1) ->η n| ∀m:Fin 1, l m ∈ setη m}⊆ Im(f,setη 0) := by
      refine' setSubsetIff.mpr _
      intro x hx; simp at hx
      replace hx:=hx  0
      simp only [Set.mem_image]
      refine' ⟨_,hx,funcEqIff.mpr _ ⟩ 
      intro n; let p4:=@p1 n
      subst p4; simp
    have p4:{l:(n:Fin 1) ->η n| ∀m:Fin 1, l m ∈ setη m}.Nonempty := by
      simp [Set.Nonempty]
      refine' Exists.elim (h 0) _
      intro map hmap
      have p5:Im(map,Set.univ).Nonempty := by
        simp [Set.Nonempty]
        exact ⟨map 0, 0 ,rfl⟩ 
      rw [hmap.symm] at p5
      let l:(n:Fin 1) ->η n := 
        fun n=>
        match n with
        | 0 => choose p5
      refine' ⟨l,_ ⟩ 
      intro m ; rw [(@p1 m).symm]
      exact choose_spec p5
    exact subsetOfCountable p4 p3 (imageOfCountable _ (h 0))
  | .succ (.succ N'') =>
    have inst':Nonempty (Fin (.succ N'')) := ⟨0⟩ 
    subst HH
    let finCoe:Fin N''.succ -> Fin N''.succ.succ := 
      fun n => 
      match n with
      | .mk val property =>
        ⟨val.succ, Nat.succ_lt_succ property⟩ 
    let η' :=fun (m:Fin N''.succ) => η (finCoe m)
    let setη' := fun (m:Fin N''.succ) => setη (finCoe m)
    have h':∀(n:Fin N''.succ),(setη' n).atMostCountable := by
      intro n ; exact h (finCoe n)
    let p1:=@finProdOfCountable _ _ inst' setη' h'
    let p2:=prodOfCountable  (h ⟨0, by simp ⟩ ) p1
    let f:(η ⟨0, by simp ⟩)× ((n:Fin N''.succ)->η' n) ->
      ((n:Fin N''.succ.succ)->η n) :=
      fun prod =>
        fun m =>
        match m with
        | .mk val property =>
          match val with
          | 0 => prod.1
          | .succ n => prod.2 ⟨n,Nat.lt_of_succ_lt_succ property ⟩ 
    have p3: {l:(n:Fin N''.succ.succ) ->η n| ∀m:Fin N''.succ.succ, l m ∈ setη m} ⊆ 
      Im(f, ((setη ⟨0,_⟩)×ˢ{l:((n:Fin N''.succ)->η' n)|∀(m),l m∈setη' m})) := by
      refine' setSubsetIff.mpr _
      intro x hx; simp only [Set.mem_image]; simp at hx
      have p4: (x 0, fun n => x (finCoe n)) ∈ 
        ((setη ⟨0,_⟩) ×ˢ {l:((n:Fin N''.succ)->η' n)|∀(m),l m∈setη' m}) := by
        simp; refine' ⟨hx 0,_ ⟩ 
        intro m; exact hx (finCoe m)
      have p5: f (x 0, fun n => x (finCoe n)) = x := by  
        refine' funcEqIff.mpr _
        intro m ; 
        match m with
        | 0 => simp
        | .mk (Nat.succ m') property =>simp
      exact ⟨_,p4,p5 ⟩ 
    have p4: {l:(n:Fin N''.succ.succ) ->η n| ∀m:Fin N''.succ.succ, l m ∈ setη m}.Nonempty := by
      have p5:∀ (n:Fin N''.succ.succ), (setη n).Nonempty := by
        intro n
        refine' Exists.elim (h n) _
        intro map hmap
        have p6:Im(map,Set.univ).Nonempty := by
          simp [Set.Nonempty]
          exact ⟨map 0, 0 ,rfl⟩ 
        rw [hmap.symm] at p6
        exact p6
      refine' ⟨fun n =>choose (p5 n),_ ⟩ 
      simp; intro m; exact choose_spec (p5 m)
    exact subsetOfCountable p4 p3 (imageOfCountable _ p2)

end COUNTABLE

