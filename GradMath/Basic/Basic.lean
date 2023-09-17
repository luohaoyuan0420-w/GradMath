import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Abel
import Mathlib.Data.Real.Basic
import GradMath.Basic.Function

universe u_1 u_2 u_3

variable {α:Type u_1} {γ:Type u_2}

namespace LOGIC

def contraposeH {p1 p2 :Prop} :(p1->p2) ->(¬p2 -> ¬p1) := by
  intro h
  contrapose! h 
  simp_all

end LOGIC

namespace NAT

lemma natLtIff {m n :Nat}: (m<n)↔ (m≠n)∧(m≤n) :=by 
  have  Pmp :(h:m<n)-> (m≠n)∧(m≤n):= by 
    intro h
    have p1:(m≠n):=
      let rec aux {m' n':Nat} (h':m'<n'):(m'≠n'):= 
        match m', n' with
        |0, 0 => 
          have rh:¬ (0<0) := by simp
          by exact (absurd h' rh )
        |0 ,.succ n''=> by
          simp [Nat.succ_ne_zero]
        |.succ m'', 0 => by
          simp [Nat.succ_ne_zero]
        |.succ m'', .succ n'' => by
          have p1: m''<n'' :=by simp [Nat.lt_of_succ_lt_succ,h']
          simp [@Nat.succ_ne_succ m'' n'',Iff.mpr,aux p1]
        aux h
    have p2:(m≤ n):=by calc 
      m ≤ m.succ := by rw [Nat.succ_eq_add_one];simp
      _ ≤ n := h
    exact ⟨p1,p2 ⟩ 
  have Pmpr: (m≠n)∧(m≤n)->(m<n):= by 
    intro h
    let h1:=h.left
    let h2:=h.right
    by_cases pd :m < n
    case pos => exact pd
    case neg =>
      have p3:n≤ m :=not_lt.mp pd
      have p4:m=n:= le_antisymm  h2 p3
      exact absurd p4 h1
  exact ⟨Pmp,Pmpr ⟩ 

lemma natLeqIff {a b:Nat}:(b≤a)↔ (∃ c:Nat,a=b+c):=
  have Pmp: (a' b':Nat)->(b'≤a')->(∃ c':Nat,a'=b'+c') :=by
    intro a'
    induction' a' with a'' hd
    case zero =>
      intro b' h1
      have p1: 0≤b':= by simp 
      have p2:b'=0:= le_antisymm h1 p1
      let c':=0
      have p3:0=b'+c':=by simp [p2]
      exact Exists.intro c' p3
    case succ =>
      intro b' h1
      match b' with
      |0 => 
        let c':=a''.succ 
        have p1: Nat.succ a'' =0 +c':=by simp
        exact Exists.intro c' p1
      |.succ b''=>
        have p1:  b'' ≤ a'':= Nat.le_of_succ_le_succ h1
        have p2:∃ c', a'' = b'' + c':=hd b'' p1
        have p3: ∀c':Nat, (p4: a''=b''+c')->
          ∃c', (Nat.succ a''=Nat.succ b''+c')
          := by
          intro c' p4
          have p5:Nat.succ a''=Nat.succ b''+c':=by
            simp [Nat.succ_eq_add_one,p4,Nat.add_assoc];rw [Nat.add_comm]
          exact ⟨c',p5⟩ 
        exact Exists.elim p2 p3
  have Pmpr:(∃ c:Nat,a=b+c)->(b≤a):= by 
    intro h1
    have p1: ∀ c:Nat, (a=b+c)->(b≤a):=by
      intro c h2;calc
        b≤ b+c := by simp
        _ = a :=Eq.symm h2
    exact Exists.elim h1 p1
  ⟨Pmp a b ,Pmpr ⟩ 

@[simp]
lemma natSubtractAdd {a b :Nat} (h1:b≤a): a-b+b=a:=
  have p1:∃c,a=b+c:=natLeqIff.mp h1
  have p2:∀c ,(p3:a=b+c)->(a-b+b=a):=by
    intro c p3
    rw [Nat.add_comm] at p3;rw [p3];simp
  Exists.elim p1 p2

end NAT

namespace SET

@[reducible]
lemma SubtypeEq {s:Set α} {e1 e2:Subtype s} (h:e1=e2):e1.val=e2.val:= by
  rw [h]

@[reducible]
lemma SubtypeNeq {s:Set α} {e1 e2:Subtype s} (h:e1≠e2):e1.val≠e2.val:= by
  by_contra hc
  have p1:e1=e2 := calc
    e1=⟨e1.val,e1.property ⟩:= by rfl
    _ =  ⟨e2.val,e2.property⟩ := by simp_rw [hc]
  exact h p1

lemma setEqIff {s t:Set α}: 
s = t ↔ ∀ (x : α), x ∈ s ↔ x ∈ t := Set.ext_iff

lemma  setSubsetIff {s t: Set α}: (s ⊆ t) ↔  ∀ (x : α), x ∈ s → x ∈ t
:=by simp [ Set.subset_def]

lemma setEqMpr {a b : Set α} :
a ⊆ b → b ⊆ a → a = b :=Set.eq_of_subset_of_subset

lemma setNotNonemptyIff {α : Type u} {s : Set α} :
¬s.Nonempty ↔ s = ∅ :=Set.not_nonempty_iff_eq_empty

lemma setNonemptyIff {α : Type u} {s : Set α} :
s.Nonempty ↔ s ≠ ∅ :=Set.nonempty_iff_ne_empty

lemma setEqEmptyIff {α : Type u} {s : Set α} :
s = ∅ ↔ ∀ (x : α), x ∉ s :=Set.eq_empty_iff_forall_not_mem

lemma setComplUnion  {α : Type u} {s t: Set α} :
(s∪t)ᶜ = sᶜ∩tᶜ :=Set.compl_union  s t 

lemma setComplInter  {α : Type u} {s t: Set α} :
(s∩t)ᶜ = sᶜ ∪ tᶜ := Set.compl_inter s t

open FUNCTION
lemma setComplSUnion {α : Type u} {S: Set (Set α)} :
(⋃₀ S)ᶜ = (⋂₀ (Im(compl,S))):= Set.compl_sUnion S

lemma setComplSInter {α : Type u} {S: Set (Set α)} :
(⋂₀  S)ᶜ = (⋃₀ (Im(compl,S))):= Set.compl_sInter S

lemma setSubsetCompl {α : Type u} {s t:  (Set α)}:
sᶜ ⊆ tᶜ ↔ t ⊆ s :=Set.compl_subset_compl

lemma setMemSUnionIff {α : Type u_1} {x : α} {S : Set (Set α)} :
x ∈ ⋃₀ S ↔ ∃ (t : Set α), t ∈ S ∧  x ∈ t := Set.mem_sUnion

lemma setMemSInterIff {α : Type u_1} {x : α} {S : Set (Set α)} :
x ∈ ⋂₀  S ↔ ∀  (t : Set α), t ∈ S -> x ∈ t := Set.mem_sInter

lemma setComplCompl {α : Type u_1} {A: Set α} : (Aᶜ)ᶜ = A := by simp

lemma foldrUnionEqSUnion {α : Type u} (S:Finset (Set α)):
S.toList.foldr (.∪.) ∅ = (⋃₀ S.toSet) := by
  refine' setEqIff.mpr _
  intro x 
  have p1 {x:α} : x∈S.toList.foldr (.∪.) ∅ ↔ ∃si,si∈S.toList∧x∈si := by
    let rec mp {L:List (Set α)} : x∈L.foldr (.∪.) ∅ -> ∃si,si∈L∧x∈si := by
      match L with
      | [] =>
        intro h1
        simp at h1
      | t::l' =>
        simp; intro h1
        cases' h1 with h1_1 h1_2
        · exact Or.inl h1_1 
        · exact Or.inr (mp h1_2)
    let rec mpr {L:List (Set α)}: (∃si,si∈L∧x∈si) -> x∈L.foldr (.∪.) ∅ := by
      intro h1
      match L with 
      | [] =>
        simp at h1
      | t::l' =>
        refine' Exists.elim h1 _
        intro si h2; simp
        let h3:=h2.left; simp at h3
        cases' h3 with h3_1 h3_2
        · rw [h3_1.symm]; exact Or.inl h2.right
        · exact Or.inr (mpr ⟨_,h3_2,h2.right⟩ )
    exact ⟨mp,mpr⟩  
  have mp: x ∈ S.toList.foldr (.∪.) ∅  -> x ∈ ⋃₀ S.toSet := by
    intro h1 
    replace h1:=p1.mp h1
    simp at h1; simp; exact h1
  have mpr:  x ∈ ⋃₀ S.toSet -> x ∈ S.toList.foldr (.∪.) ∅ := by
    intro h1
    have h2:∃si,si∈S.toList∧x∈si := by
      simp; simp at h1; exact h1
    exact p1.mpr h2
  exact ⟨mp,mpr⟩ 

lemma foldrInterEqSInter {α : Type u} (S:Finset (Set α)) :
S.toList.foldr (.∩.) Set.univ = (⋂₀ S.toSet) := by
  refine' setEqIff.mpr _
  intro x 
  have p1 {x:α} : x∈S.toList.foldr (.∩.) Set.univ ↔ ∀si,si∈S.toList->x∈si := by
    let rec mp {L:List (Set α)} : x∈L.foldr (.∩.) Set.univ -> (∀si,si∈L->x∈si)  := by
      match L with
      | [] => simp
      | t::l' =>
        simp; intro h1 h2
        exact ⟨h1,mp h2 ⟩ 
    let rec mpr {L:List (Set α)}:(∀si,si∈L->x∈si)->x∈L.foldr (.∩.) Set.univ:= by
      intro h1
      match L with 
      | [] => simp
      | t::l' =>
        simp 
        have p2:t∈ t::l' := by simp
        have p3:∀ (si : Set α), si ∈ l' → x ∈ si := by
          intro si h2
          have p4:si ∈ t :: l' := by simp; exact Or.inr h2
          exact h1 _ p4
        exact ⟨h1 _ p2,mpr p3 ⟩ 
    exact ⟨mp,mpr⟩  
  have mp: x  ∈ S.toList.foldr (.∩.) Set.univ -> x ∈(⋂₀ S.toSet) := by
    intro h1 
    replace h1:=p1.mp h1
    simp at h1; simp; exact h1
  have mpr:  x ∈(⋂₀ S.toSet)-> x  ∈ S.toList.foldr (.∩.) Set.univ:= by
    intro h1
    have h2:(∀si,si∈S.toList->x∈si)  := by
      simp; simp at h1; exact h1
    exact p1.mpr h2
  exact ⟨mp,mpr⟩ 

lemma setDiffDef {α : Type u}{s t : Set α} :s\t = s∩(tᶜ ) := 
Set.diff_eq s t

lemma setMemDiffIff {α : Type u} {s t:Set α} {x : α} :
x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := Set.mem_diff x

lemma setMemUnionIff {α : Type u} {x : α} {a b : Set α} :
x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b :=Set.mem_union x a b

lemma setMemInterIff {α : Type u}{x:α}{a b:Set α}:(x∈a∧x∈b) ↔ x ∈ a ∩ b :=by
  have mp: (x∈a∧x∈b) -> x ∈ a ∩ b := by
    intro h1; simp; exact h1
  have mpr:  x ∈ a ∩ b ->  (x∈a∧x∈b) := by
    intro h1 ; simp at h1; exact h1
  exact ⟨mp,mpr⟩ 

lemma setSUnionEqUnion {S:Set (Set α)}:⋃₀ S = ⋃ (i:(Subtype S)), i.val := by 
  refine' setEqIff.mpr _
  intro a; simp
  have mp: (∃ t, t ∈ S ∧ a ∈ t) ->∃ a_1, S a_1 ∧ a ∈ a_1 := by
    intro h1; exact h1
  have mpr: (∃ a_1, S a_1 ∧ a ∈ a_1) ->(∃ t, t ∈ S ∧ a ∈ t) := by 
    intro h1; exact h1
  exact ⟨mp,mpr⟩ 

lemma setSInterEqInter {S:Set (Set α)}:⋂₀ S = ⋂ (i:(Subtype S)), i.val := by
  refine' setEqIff.mpr _
  intro a; simp
  have mp: (∀ (t : Set α), t ∈ S → a ∈ t) -> ∀ (a_1 : Set α), S a_1 → a ∈ a_1 := by
    intro h1; exact h1
  have mpr: (∀ (a_1 : Set α), S a_1 → a ∈ a_1) ->∀ (t : Set α), t ∈ S → a ∈ t := by
    intro h1; exact h1
  exact ⟨mp,mpr⟩ 

lemma setUnionEqSUnion {ι:Type u_1} {s:ι→Set α}:(⋃ (i:ι), s i )= ⋃₀ Im(s,(Set.univ:Set ι)) := by
  simp

lemma setInterEqSInter {ι:Type u_1} {s:ι→Set α}:(⋂ (i:ι), s i )= ⋂₀  Im(s,(Set.univ:Set ι)) := by
  simp

variable (s:Set α)
instance : CoeDep (Subtype s) ⟨v,h⟩   α where   
  coe:=v

end SET

namespace Set

@[simp]
def atMostCountable {α :Type u_1} (s:Set α) :Prop :=
∃(f:ℕ->α), s= Im(f,univ)

end Set

namespace LIST

lemma listMemMapMpr  (f : α → γ) {a : α} {l : List α} (h : a ∈ l) :
  f a ∈ l.map f := List.mem_map_of_mem f h

lemma listMemMapIff {α : Type u} {β : Type v} {f : α → β} {b : β} {l : List α} :
  b ∈ List.map f l ↔ ∃ (a : α), a ∈ l ∧ f a = b := List.mem_map

lemma listNonEmpty  {l:List α} (h:0< l.length) :l = l[0]::(l.drop 1):= by
  match l with
  |[] =>
    have p1:¬(0<0):= by simp
    have rp1: (0<0):= by calc
      0 < List.length [] := h
      _ = 0 := by simp
    exact  (absurd  rp1 p1)
  |a::l'=>simp 

lemma consListIndxAddOne {i:Nat} {l:List α} (a:α) (p:i<l.length) 
  {p':i+1<(a::l).length}:
  (a::l)[i+1] = l[i] :=by  simp

lemma listEqIff {l1 l2:List α}: 
l1=l2 ↔ (l1.length=l2.length)∧(∀{n:Nat},
    (h1:n<l1.length)->{h2:n<l2.length} -> l1[n]=l2[n]):= 
  have Pmp: (l1=l2)->(l1.length=l2.length)∧(∀{n:Nat},
    (h1:n<l1.length)->(h2:n<l2.length) -> l1[n]=l2[n]):= by
    intro p1 
    simp [p1]
  have Pmpr: {l1' l2':List α}->(l1'.length=l2'.length)∧
    (∀{n':Nat}, (h1':n'<l1'.length)->(h2':n'<l2'.length) -> l1'[n']=l2'[n'])
    ->(l1'=l2'):= by 
    intro l1'
    induction' l1' with a l1'' hd
    case nil =>
      intro  l2' p
      let p1:=p.left
      have p3:l2'.length=0 := by rw [<-p1];simp
      have p4:l2'=[]:=List.length_eq_zero.mp p3
      simp [p4]
    case cons =>
      intro l2' p
      let p3:=p.left
      let p4:∀{n':ℕ} (h1':n'<List.length (a::l1''))(h2':n'<List.length l2'),
        (a::l1'')[n'] = l2'[n']:=p.right
      have p5:0 < (a::l1'').length := by simp
      have p6:0<l2'.length := by calc 
        0 < (a::l1'').length := by simp
        _ = l2'.length := by rw [p3]
      let b:=l2'[0]
      let l2'':=(l2'.drop 1)
      have p8: l2'=b::l2'':=by calc
        l2'=l2'[0]::(l2'.drop 1) :=listNonEmpty p6
        _ = b::l2'' := rfl
      have p9:a=b:=  by calc
        a = (a :: l1'')[0] :=by simp
        _ = l2'[0] := by rw [<-(p4 p5 p6)] 
        _ = b := by rfl
      have p10: ∀{n'':ℕ}(h1'':n''< l1''.length) (h2'':n''< l2''.length),
        l1''[n'']=l2''[n'']:= by
        intro n'' h1'' h2''
        have p10_1:n''.succ < (a::l1'').length := by simp [h1'',Nat.succ_lt_succ]
        have p10_2:n''.succ < (l2').length := by calc 
          n''.succ < l2''.length.succ :=Nat.succ_lt_succ h2''
          _ = (b::l2'').length := by simp
          _ = l2'.length := by rw [<-p8]
        have p10_3:n''.succ<(b::l2'').length:= by rw [<-p8];exact p10_2
        have p10_4 {list1 list2:List α }{m:Nat}{hy1:m<list1.length}{hy2:m<list2.length}
           (hy3:list1=list2) :list1[m]=list2[m]:= by simp [hy3]
        calc 
          l1''[n''] = (a::l1'')[n''.succ] := by simp
          _ = l2'[n''.succ] := p4 p10_1 p10_2
          _ = (b::l2'')[n''.succ] :=  p10_4 p8
          _ = l2''[n''] := by simp
      have p11: l1''.length = l2''.length :=by calc
          l1''.length = l1''.length.succ -1:= by simp
          _ = (a :: l1'').length -1 := by simp
          _ = l2'.length -1 := congr_arg (.-1) p3
          _ = (b::l2'').length -1 :=by rw [p8]
          _ = l2''.length.succ -1 := by simp
          _ = l2''.length := by simp
      rw [p9,p8,hd ⟨p11,p10⟩];
  ⟨Pmp,Pmpr ⟩ 

lemma listNeqMpr {l1 l2:List α} {n:Nat}(h1:n<l1.length)(h2:n<l2.length)
(H:l1[n]≠l2[n]):l1≠l2:=by
  by_contra hc
  have p1:l1[n]=l2[n]:= by simp_all
  exact H p1

lemma listIndexSubsti {l:List α } {n m:Nat} (h1:n<l.length) (h2:n=m)
  (h':m<l.length:=h2▸h1): (l[n]=l[m]) := by simp [h1,h2]
     
/-
def sublistMemL (l1 l2:List α) (a:α): a∈l1->(a∈(l1++l2)):=by 
  intro h ;simp
  exact (Or.intro_left _ h)

def  sublistMemR (l1 l2:List α) (a:α): a∈l2->(a∈(l1++l2)):=by
  intro h ;simp
  exact (Or.intro_right _ h)

-/
lemma listMemSplit {α:Type u}{a:α}{l:List α}(h: a∈l):
  ∃ s t, l = s ++ a :: t 
  := List.mem_split h

lemma listTakeLenLeq {l:List α} {n:Nat} (h:n≤l.length): 
  (l.take n).length = n :=
  let rec aux {l':List α } {n':Nat} (h':n'≤l'.length)
    : (l'.take n').length=n' := by
    let selfV:=n'
    have selfH':n'=selfV:=by rfl
    match n' with
    |0 => simp
    |.succ n''=>
      have selfH:n'=.succ n'':= by simp [selfH']
      have p1: 0<l'.length:=by calc
        0<1 := by simp
        1 ≤  n''+1 :=by simp
        _ = .succ n'':=by simp [Nat.add_one]
        _ ≤ l'.length:= by simp [selfH,h']
      have p2: l'=l'[0]::(l'.drop 1):=listNonEmpty _
      let a:=l'[0]
      let l'':=l'.drop 1
      have p3: l'=a::l'':= by calc
        l' = l'[0]::(l'.drop 1) := p2
        _ = a::l'' := by simp
      have p4: l'.take n'= a::(l''.take (n'')) := by calc
        l'.take n' = (a::l'').take (.succ n'') := by rw [p3,selfH]
        _ = a::(l''.take (n'')):= by simp
      have p5:l'.length = l''.length+1 :=by calc
        l'.length = (a::l'').length := by rw [p3]
        _ =l''.length+1 := by simp
      have p6:n''≤l''.length:=by 
        have p6_1:n''+1≤l'.length:=by rw [<-Nat.succ_eq_add_one];simp [selfH,h']
        have p6_2:n''+1≤l''.length+1 := by calc
          n''+1 ≤ l'.length := p6_1
          _ = l''.length+1 := p5
        exact Nat.le_of_add_le_add_right p6_2
      have p8:(l''.take n'').length=n'' := aux p6
      have p9:{j:List α}->((a::j).length=j.length+1):=by simp
      rw [<-selfH,p4,p9,p8];simp[selfH]
  aux h

lemma listTakeLenGeq {n:ℕ}{l:List α}: l.length≤ n → l.take n = l:=
  List.take_all_of_le

lemma listDropLenLeq {l:List α} {n:Nat} (h:n≤l.length):
  (l.drop n).length = l.length - n:= 
  let rec aux {l':List α} {n':Nat} (h':n'≤l'.length):
  (l'.drop n').length = l'.length - n':= by
    let selfV:=n'
    have selfH':n'=selfV:=by rfl
    match n' with
    |0=> simp
    |.succ n''=>
      have selfH:n'=.succ n'':= by simp [selfH']
      have p1: 0<l'.length:=by calc
        0<1 := by simp
        1 ≤  n''+1 :=by simp
        _ = .succ n'':=by simp [Nat.add_one]
        _ ≤ l'.length:= by simp [selfH,h']
      have p2: l'=l'[0]::(l'.drop 1):=listNonEmpty _
      let a:=l'[0]
      let l'':=l'.drop 1
      have p3: l'=a::l'':= by calc
        l' = l'[0]::(l'.drop 1) := p2
        _ = a::l'' := by simp
      have p4: l'.drop (.succ n'')=l''.drop n'' :=by calc
        l'.drop (.succ n'') = (a::l'').drop (.succ n'') :=by rw [p3]
        _ = l''.drop n'' := by simp
      have p5:l'.length = l''.length+1 :=by calc
        l'.length = (a::l'').length := by rw [p3]
        _ =l''.length+1 := by simp
      have p6:n''≤l''.length:=by 
        have p6_1:n''+1≤l'.length:=by rw [<-Nat.succ_eq_add_one];simp [selfH,h']
        have p6_2:n''+1≤l''.length+1 := by calc
          n''+1 ≤ l'.length := p6_1
          _ = l''.length+1 := p5
        exact Nat.le_of_add_le_add_right p6_2
      have p7:(l''.drop n'').length = l''.length - n'':=aux p6
      rw [p4,p7,p5];simp 
  aux h

lemma listSplit  {l:List α} {n:Nat} (h:n≤ l.length):
  l=(l.take n)++(l.drop n):=
  let rec aux  {l':List α} {n':Nat} (h':n'≤ l'.length):
  l'=(l'.take n')++(l'.drop n'):=by
    let selfV:=n'
    have selfH':n'=selfV:=by rfl
    match n' with
    |0=> simp
    |.succ n''=>
      have selfH:n'=.succ n'':= by simp [selfH']
      have p1: 0<l'.length:=by calc
        0<n''.succ := by simp 
        _ ≤ l'.length:= h'
      have p2: l'=l'[0]::(l'.drop 1):=listNonEmpty _
      let a:=l'[0]
      let l'':=l'.drop 1
      have p3: l'=a::l'':= by calc
        l' = l'[0]::(l'.drop 1) := p2
        _ = a::l'' := by simp
      have p5:l'.length = l''.length+1 :=by calc
        l'.length = (a::l'').length := by rw [p3]
        _ =l''.length+1 := by simp
      have p6:n''≤l''.length:=by 
        have p6_1:n''+1≤l'.length:=by rw [<-Nat.succ_eq_add_one];simp [selfH,h']
        have p6_2:(n'').succ≤(l''.length).succ := by calc
          n''+1 ≤ l'.length := p6_1
          _ = l''.length+1 := p5
        exact Nat.le_of_succ_le_succ p6_2
      have p7: l''=(l''.take n'')++(l''.drop n''):=aux p6
      have p4_1:(l').take (.succ n'')=a::(l''.take n'') := by calc
        (l').take (.succ n'') = (a::l'').take (.succ n'') := by rw [p3]
        _ =a::(l''.take n'') := by simp
      have p4_2:(l').drop (.succ n'')=(l''.drop n''):= by calc
        (l').drop (.succ n'') = (a::l'').drop (.succ n'') := by rw [p3]
        _ = (l''.drop n'') := by simp
      calc
        l' = a::l'' := p3
        _ =a::( (l''.take n'')++(l''.drop n'')) :=by simp [p7]
        _ = (a::(l''.take n''))++(l''.drop n'') := by simp
        _ = (l').take (.succ n'')++(l'.drop (.succ n'')) := by rw [<-p4_1,<-p4_2]
  aux h

lemma listSplitByElem {a:α} {n:Nat} {l:List α} (h1:n<l.length) (h2:l[n] =a ):
  (l=(l.take n)++[a]++(l.drop (n+1))):=
  let aux :{a':α}->{n':Nat}->(l':List α)->(h1':n'<l'.length)->(h2':l'[n'] =a')
    ->(l'=(l'.take n')++[a']++(l'.drop (n'+1))):=by
    intro a' n' 
    induction' n' with n'' hd
    case zero =>
      intro l' h1' h2'
      have p1: l' = l'[0]::(l'.drop 1) :=listNonEmpty h1'
      have p2: l' = a'::(l'.drop 1) := by calc
        l'= l'[0]::(l'.drop 1) :=p1
        _=a'::(l'.drop 1) := by rw [h2']
      apply Eq.symm
      calc
        List.take Nat.zero l' ++[a']++ l'.drop (0+1) = a'::(l'.drop 1):=by simp
        _ = l' :=by rw [p2];simp
    case succ =>
      intro l' h1' h2'     
      have p0:0<l'.length :=by calc
        0 ≤ Nat.succ n'' := by simp
        _ < List.length l' := h1'
      have p1 : l'=l'[0]::(l'.drop 1) :=listNonEmpty p0
      let b:=l'[0]
      let l'':=(l'.drop 1)
      have p2: l'=b::l'' :=p1
      have p2': b::l''=l' :=by rw [p2]
      have p3: l'.take (Nat.succ n'') = b::(l''.take n''):=by
        rw [p2];simp
      have p4: l'.drop (Nat.succ (n''+1)) = l''.drop (n''+1) := by
        rw [p2];simp
      have p5: n''<l''.length := 
        have p5': (n'').succ < (List.length l'').succ:= by calc
          Nat.succ n'' < List.length l' := h1'
          _ = (b::l'').length := by rw [p2]
          _ = List.length l''+1 := by simp
        Nat.lt_of_succ_lt_succ p5'
      have p6: l''[n'']=a':= by
        rw [<-h2']
        have p6': Nat.succ n''<(b::l'').length:= by calc
          Nat.succ n''= n'' +1:= by simp
          _ < l''.length +1 := Nat.succ_lt_succ p5
          _ = (b::l'').length := by simp
        have p6'':(b::l'')[Nat.succ n'']=l'[Nat.succ n'']
          :=  (listEqIff.mp p2').right _
        calc
          l''[n''] = (b::l'')[n'' +1]:= by simp
          _= l'[Nat.succ n''] :=p6''
      have p7:l''=(l''.take n'')++[a']++(l''.drop (n''+1))
        := hd l'' p5 p6
      rw [p3,p4,p2];
      exact congr_arg (fun list=>b::list) p7
  aux l h1 h2
      
lemma listTakeLeft {n:ℕ}(l1 l2:List α)(h:List.length l1 =n):
  List.take n (l1 ++ l2) = l1 := List.take_left' h

lemma listDropLeft {l1:List α}{l2:List α}{n:ℕ}(h:List.length l1 =n):
  List.drop n (l1 ++ l2) = l2 := List.drop_left' h

lemma listTakeTake (n:ℕ)(m:ℕ)(l:List α):
  List.take n (List.take m l) = List.take (min n m) l
  :=List.take_take n m l

lemma listDropTake (m:ℕ)(n:ℕ)(l:List α):
  List.drop m (List.take (m + n) l) = List.take n (List.drop m l)
  :=List.drop_take m n l

lemma listDropDrop (n : ℕ) (m : ℕ) (l : List α) :
  List.drop n (List.drop m l) = List.drop (n + m) l
  :=List.drop_drop n m l

@[simp]
lemma listNotNilIsNotZero {l:List α}: l≠[]→ 0<List.length l
  :=List.length_pos_of_ne_nil

@[simp]
lemma listNotZeroIsNotNil {l:List α}: 0 < List.length l → l ≠ []
  := List.ne_nil_of_length_pos

def listSplitByElemRev.f1 {a:α} {l:List α} {l1 l2:List α} (h:l=l1++[a]++l2):
  l1.length<l.length:= 
  have p1:l1.length<(l1++[a]++l2).length:=by simp
  Eq.symm (h) ▸ p1

lemma listSplitByElemRev {a:α} {l:List α} {l1 l2:List α} (h:l=l1++[a]++l2) 
  (h':l1.length<l.length:=listSplitByElemRev.f1 h)
  :(l[l1.length] = a):=by 
  have p1 {L:List α}{b:α } (h2:L.length<(L++[b]).length):
    ((L++[b]).getLast _) = (L++[b])[L.length]:=by 
    have p1_1:(L++[b]).length - 1<(L++[b]).length:=by simp
    have p1_2: List.get (L ++ [b]) { val:=(L++[b]).length-1,isLt:=p1_1} =
      List.getLast (L ++ [b]) (_ : L ++ [b] = [] → False)
      :=List.get_length_sub_one p1_1
    have p1_3:List.get (L ++ [b]) { val:=(L++[b]).length-1,isLt:=p1_1}
      =(L++[b])[L.length] := by simp
    rw [ p1_3] at p1_2;rw [p1_2];simp
    intro L h1;
    have p2: 0< ( L ++ [a]).length:=by simp
    simp [p2]
  let a':=l[l1.length]
  have p4:a'=l[l1.length] := rfl
  let l1':=l.take l1.length
  let l2':=l.drop (l1.length+1)
  have p2:(l1'++[a']).length=l1'.length+1 := by simp
  have p3:l=l1'++[a']++l2':=listSplitByElem h' p4
  have p4:l.take (l1'.length+1)=l1'++[a']:= by 
    rw [p3];
    exact listTakeLeft _ _  p2
  have p6:(l1++[a]).length=l1.length+1:= by simp
  have p7:l.take (l1.length+1)=l1++[a]:=by
    rw [h];
    exact listTakeLeft _ _ p6
  have p8:l1.length≤l.length:= (NAT.natLtIff.mp h').right
  have p9:l1'.length=l1.length:=listTakeLenLeq p8
  rw [p9,p7] at p4
  apply Eq.symm
  have p10:l1.length<(l1 ++ [a]).length:= by simp
  have p11:l1'.length<(l1'++[a'] ).length:= by simp
  have p12:l1'.length<(l1++[a]).length:= by calc
    l1'.length<(l1'++[a'] ).length := p11
    _ = (l1++[a]).length := by rw [p4]
  calc
    a = (l1 ++ [a]).getLast (by simp):=by simp
    _ = (l1 ++ [a])[l1.length] := p1 (by simp)
    _ = (l1++[a])[l1'.length] := listIndexSubsti p10 (Eq.symm p9)
    _ = (l1'++[a'])[l1'.length]:=
      by simp [listEqIff,Iff.mp,Iff.mpr,p4,And.right,And.left,p12]
    _ = (l1'++[a']).getLast (by simp) :=Eq.symm  (p1   p11)
    _ = a' := by simp
         
lemma listTakeIsSublist {l:List α}{n i:Nat}(h1:n≤ l.length) (h2:i<n)
  (h3:i<(l.take n).length:=(Eq.symm (listTakeLenLeq h1)) ▸ h2 )
  (h4:i<l.length:=lt_of_lt_of_le h2 h1): 
  (l.take n)[i]=l[i]:=by 
  let l':= (l.take n)
  let l3:= (l.drop (n))
  have p1:l=l'++l3:=listSplit h1
  let a:=(l'[i])
  have p2:l'[i]=a := by rfl
  let l1:=(l.take n).take i
  let l2:=(l.take n).drop (i+1)
  have p3:l'=l1++[a]++l2:=listSplitByElem h3 p2
  rw [p3] at p1
  have p4:l1.length=i 
    := listTakeLenLeq ((NAT.natLtIff.mp h3).right)
  have p5:l1.length<l.length:= by rw [p4];exact (lt_of_lt_of_le h2 h1)
  have p6:  (l1 ++ [a] ++ l2 ++ l3)= l1 ++ [a] ++ (l2 ++ l3)
    := by simp
  rw [p6] at p1
  have p7:l[i] = a :=by calc
    l[i] = l[l1.length]:= listIndexSubsti (lt_of_lt_of_le h2 h1) (Eq.symm p4)
    _ = a := (listSplitByElemRev  p1 )
  exact Eq.symm p7

def listDropIsSublist.f1 {i m n :Nat} (h1:n≤m) (h2:i<m-n) : (i+n<m) := calc
  i+n < m-n+n :=Nat.add_lt_add_right h2 _
  _ = m :=by simp [h1]

lemma listDropIsSublist {l:List α}{n i:Nat}(h1:n≤ l.length) (h2:i<l.length-n)
(h3:i<(l.drop n).length:=(listDropLenLeq h1).symm ▸ h2)
(h4: i+n<l.length:=listDropIsSublist.f1 h1 h2):
(l.drop n)[i] = l[i+n] := by 
  set a:=l[i+n] with ← h5
  let p1:= listSplitByElem h4 h5
  have p2: (l.take (i+n)).length = i+n:=listTakeLenLeq (NAT.natLtIff.mp h4).2
  let p3:=listSplit ((by simp [p2,h1]):n≤(l.take (i+n)).length)
  have p4:(l.take (i+n)).take n = l.take n:= by simp [listTakeTake]
  rw [p4] at p3; rw [p3] at p1
  let p5:=listSplit h1
  have p6:l.take n ++ l.drop n = l.take n ++ ((l.take (i+n)).drop n ++ [a] ++ l.drop (i+n+1) )
    := calc
    _ = l.take n ++ (l.take (i+n)).drop n ++ [a] ++ l.drop (i+n+1) 
      :=Eq.trans p5.symm p1
    _ = _ := by simp
  replace p6:=List.append_left_cancel p6;
  replace p6:=calc 
    List.drop n l =(l.take (i+n)).drop n ++ [a] ++ l.drop (i+n+1) := p6
    _ = (l.take (n+i)).drop n ++ [a] ++ l.drop ((i+1) +n):= by simp [add_comm,add_assoc]
    _ = (l.drop n).take i ++[a]++ (l.drop n).drop (i+1):= by rw [listDropTake,← listDropDrop]
  replace p6:=listSplitByElemRev p6
  let p7:=listDropLenLeq h1
  replace p7:=listTakeLenLeq (NAT.natLtIff.mp (p7.symm ▸ h2)).2
  exact (listIndexSubsti  h3 p7.symm ) ▸ p6

lemma listSplitRev {l l1 l2:List α} (h:l=l1++l2):
(l1=l.take l1.length)∧(l2=l.drop l1.length):= by 
  have h1:l.length = l1.length + l2.length:= by simp [h]
  replace h1:l1.length≤l.length := by simp [h1]
  have p2:(l1++l2).take l1.length = l1:= by simp
  rw [<- h] at p2;rw [<- p2] at h;
  have p3:=Eq.trans h.symm (listSplit h1)
  exact ⟨p2.symm,List.append_left_cancel p3 ⟩ 

lemma listMemOfSumIff {a:α}{l1 l2:List α}:
(a ∈ l1++l2) ↔ (a∈l1)∨(a∈l2) :=by simp

@[simp]
lemma listGetIsMem {n:Nat}{l:List α} (h:n<l.length):l[n]∈l:= by 
  let a:=l[n]
  let p1:=listSplitByElem h ((by rfl):l[n]=a)
  have p2: a∈List.take n l ++ [a] := by simp
  replace p2: a∈ l.take n ++ [a] ++ l.drop (n+1):= by simp [p2]
  rw [← p1] at p2;exact p2

lemma listMemIff {a:α}{l:List α}: (a∈l )↔ ( ∃ (n:Nat) (h:n<l.length), l[n]=a ):= by
  have mp :(h: a∈l )->( ∃ (n:Nat) (h:n<l.length), l[n]=a ):= by
    intro h
    let p1:= listMemSplit h
    exact Exists.elim p1 (by
      intro s h2
      exact Exists.elim h2 (by 
        intro t h3
        replace h3:l= s++[a]++t:= by simp [h3]
        let p2:=listSplitByElemRev h3
        have p3:s.length<l.length := by simp_all
        exact ⟨s.length,p3,p2 ⟩ ))
  have mpr: (H:∃(n:Nat) (h:n<l.length), l[n]=a) ->( a∈l ):= by
    intro H
    exact Exists.elim H (by
      intro n h2
      exact Exists.elim h2 (by 
        intro h3 h4
        have p1:n<l.length := by simp_all
        replace p1:= listGetIsMem  p1
        exact h4▸ p1
        ))
  exact ⟨mp,mpr ⟩  

lemma listNotMemIff {l:List α} {a:α}:
a∉l ↔ (∀{i:Nat},(h:i<l.length)->a≠l[i]):= by
  have mp:a∉l->(∀{i:Nat},(h:i<l.length)->a≠l[i]):= by
    intro h1 i h2
    by_contra hc
    let p1:=listGetIsMem h2;rw [<- hc] at p1
    exact  h1 p1
  have mpr:(∀{i:Nat},(h:i<l.length)->a≠l[i])->a∉l:= by
    intro i 
    by_contra hc
    let p1:=listMemSplit hc
    have p2:∀ s t, l = s ++ a::t -> False:= by
      intro s t p3 
      replace p3:l= s ++[a]++ t:= by simp [p3]
      have p4:s.length<l.length:= by simp_all
      let p5:=listSplitByElemRev p3
      replace i:=i p4
      exact i p5.symm
    have p3:∀ s, (∃ t,l = s ++ a::t )-> False:= 
      fun s p => Exists.elim p (p2 s)
    exact Exists.elim p1 p3
  exact ⟨mp,mpr⟩ 

lemma listNodupIff {l:List α}:
l.Nodup ↔ ∀{i j:Nat},(h1:i<l.length)->(h2:j<l.length)->(i≠j)->(l[i]≠l[j]) := 
  let mpr: (∀{i j:Nat},(h1:i<l.length)->(h2:j<l.length)->(i≠j)->(l[i]≠l[j]))
  ->l.Nodup:= by
    intro p
    induction' l with a l' hd
    case nil => simp
    case cons => 
      have p1: (∀{i j:ℕ}(h1:i<l'.length)(h2:j<l'.length),i≠j → l'[i]≠l'[j])
      := by
        intro i j h1 h2 h3
        have p2:i+1< (a::l').length:= by simp [h1,Nat.succ_lt_succ]
        have p3:j+1<(a::l').length:= by simp [h2,Nat.succ_lt_succ]
        have p4:i+1≠ j+1:= by simp_all
        let p5:=p p2 p3 p4
        simp at p5;exact p5
      replace hd:= hd p1
      have p2:∀ {i:Nat},(h:i<l'.length)->(a≠ l'[i]):=by
        intro j h3
        have p3:j+1< List.length (a :: l'):= by simp [h3,Nat.succ_lt_succ]
        have p5:0≠ j+1:= ((@NAT.natLtIff 0 (j+1)).mp (by simp) ).1
        let p4:=@p 0 (j+1) (by simp_all) p3 p5 
        simp at p4;exact p4
      replace p2:=listNotMemIff.mpr p2
      simp_all
  let mp:l.Nodup->
     ∀{i j:Nat},(h1:i<l.length)->(h2:j<l.length)->(i≠j)->(l[i]≠l[j]) :=by
    induction' l with a l' hd
    case nil =>
      intro _ m n H1 H2
      have P1:0≤ m:= by simp
      exact absurd P1 (by simp_all) 
    case cons =>
      intro H m n H1 H2 H3
      set l:=a :: l' with H0
      match m, n with  
        |.zero , .zero =>
          exact absurd (by simp_all) H3 
        |.succ m' ,.zero => 
          rw [H0] at H;simp at H;
          have P1: (a :: l')[Nat.zero] =a := by simp
          rw [H0] at H1;simp at H1
          have P2': m'<List.length l':= Nat.lt_of_succ_lt_succ H1
          have P2:(a::l')[m'.succ]=l'[m']:= by simp
          rw [P1,P2]
          have P3: l'[m']∈ l':= LIST.listGetIsMem P2'
          simp;simp at P3;
          by_contra hc
          replace H:=H.1;rw [← hc] at H;
          exact H P3 
        |.zero, .succ n' => 
          rw [H0] at H;simp at H;
          have P1: (a :: l')[Nat.zero] =a := by simp
          rw [H0] at H1;simp at H1
          have P2': n'<List.length l':= Nat.lt_of_succ_lt_succ H2
          have P2:(a::l')[n'.succ]=l'[n']:= by simp
          rw [P1,P2];
          have P3: l'[n']∈ l':= LIST.listGetIsMem P2'
          simp;simp at P3;
          by_contra hc
          replace H:=H.1;rw [hc] at H;
          exact H P3  
        |.succ m', .succ n' =>         
          have P1': m' <l'.length:=by 
            rw [H0] at H1;simp at H1; 
            exact Nat.lt_of_succ_lt_succ H1
          have P2': n'<l'.length:= by
            rw [H0] at H2;simp at H2; 
            exact Nat.lt_of_succ_lt_succ H2
          have P1:(a :: l')[Nat.succ m'] = l'[m']:= by simp 
          have P2:(a :: l')[Nat.succ n'] = l'[n']:= by simp
          rw [P1,P2];rw [H0] at H;simp at H;
          exact hd H.2 P1' P2' (by simp_all)    
  ⟨mp,mpr ⟩ 

--@[simp]
lemma listNodupCons {a:α} {l:List α}:
(a::l).Nodup ↔ a ∉ l ∧ l.Nodup :=List.nodup_cons

lemma listNodupLenEqOne {l:List α} (h:l.length=1) :(l.Nodup):= by
  match l with
  |[] => simp 
  | a::l' =>
    simp at h;
    have p1:l'=[] := List.length_eq_zero.mp h
    have p2: l'.Nodup := by simp [p1]
    have p3: a∉l' := by simp [p1]
    exact listNodupCons.mpr ⟨p3,p2 ⟩ 

lemma listTakeLenLeqOrig {n:ℕ}{l:List α}: (l.take n).length≤l.length:= by
  by_cases c: n≤l.length
  · let p1:= listTakeLenLeq c
    rw [p1];exact c
  · push_neg at c
    let p1: l.length ≤ n :=(NAT.natLtIff.mp c).2
    rw [listTakeLenGeq p1] 

lemma listDropLenLeqOrig {n:ℕ}{l:List α}: (l.drop n).length≤l.length:= by
  by_cases c: n≤l.length
  · let p1:= listDropLenLeq c
    rw [p1];simp
  · push_neg at c
    let p1: l.length ≤ n :=(NAT.natLtIff.mp c).2
    replace p1: n- l.length + l.length =n :=NAT.natSubtractAdd p1
    calc
      (l.drop n).length = (l.drop (n- l.length + l.length)).length
          := by simp [p1]
      _ = ((l.drop (l.length)).drop (n- l.length)).length
          := by simp [(listDropDrop (n- l.length) l.length _ )]
      _ = 0 := by simp
      _ ≤ l.length := by simp

lemma listMapNEqFN (l:List α) {n:Nat} (f:α->γ) (h:n<l.length)
(h':n<(l.map f).length:=List.length_map l f ▸ h): (l.map f)[n]=f l[n] := by
  simp

end LIST

namespace List

def flatten: (List (List α))->List α:= 
  let rec f (r:List α) (l:List (List α)) :List α :=
    match l with
    | [] => r
    | a::l' => f (r++a) l'
  fun l => f [] l

def indexRecover.f.p1 (n:Nat)(l':List Nat):n + l'.foldl (.+.) 0=l'.foldl (.+.) n:= by
  match l' with
  |[] => simp
  |m::l'' =>
    simp
    let p3:= indexRecover.f.p1 (n+m) l''
    let p4:= indexRecover.f.p1 m l''
    rw [p3.symm,p4.symm];abel

def indexRecover.f {n:Nat} (m:Nat) (l:List Nat) (h:n<l.foldl (.+.) 0 ):Nat×Nat:=
  match l with 
  |[] => by simp at h
  |i::l' => by
    by_cases c1: n<i
    · exact (m,n)
    · push_neg at c1
      simp at h;
      rw [(indexRecover.f.p1 i l').symm] at h
      have p1: (n-i)+i <  (l'.foldl (.+.) 0) + i :=calc 
        (n-i)+i = n := NAT.natSubtractAdd c1
        _ < i + (l'.foldl (.+.) 0) := h
        _ =_ := by simp [add_comm]
      simp at p1
      exact indexRecover.f (m+1) l' p1

end List

namespace LIST

lemma flatLenEqSum (l:List (List α)): 
l.flatten.length=(l.map (fun a=>a.length)).foldl (.+.) 0:= by
  induction' l with a l' h
  case nil => rfl
  case cons => 
    rw [List.flatten,List.flatten.f];simp;
    let rec p1 {r':List α} {l':List (List α)} :
      ( List.flatten.f r' l').length=r'.length+ (List.flatten.f [] l').length:=by
      match l' with
      |[] => simp [List.flatten.f]
      |a::l'' =>
        simp [List.flatten.f]
        let p2:=@p1 (r'++a) l'';
        let p3:=@p1 (a) l'';
        rw [p2,p3];simp;abel
    rw [p1];rw [List.flatten] at h;rw [h]
    rw [List.indexRecover.f.p1]

lemma flatSumEqSumFlat {l1 l2:List (List α)}: (l1++l2).flatten= l1.flatten ++ l2.flatten:=by
  match l1 with
  |[] => rfl
  |a::l1' =>
    have p1: (a::l1'++l2) = a::(l1'++l2):= by simp
    rw [p1];simp [List.flatten,List.flatten.f]
    let rec p2 {b:List α} {l':List (List α)} : 
      List.flatten.f b l' = b ++ List.flatten.f [] l':= by
      match l' with
      |[] => simp [List.flatten.f]
      |c::l'' => 
        simp [List.flatten.f]
        let p3:=@p2 (b++c) l''
        let p4:=@p2 c l''
        rw [p3,p4];simp
    rw [@p2 a _ ,@p2 a _];
    let p3:= @flatSumEqSumFlat l1' l2;
    simp [List.flatten] at p3; rw [p3];simp

lemma flatMemMpr {a:α}{l:List α}(L: List (List α))(h1:a∈l) (h2:l∈L) :a∈L.flatten:= by 
  let p1:=(@listMemIff _ l L ).mp h2
  let p2:=(@listMemIff _ a l ).mp h1
  exact Exists.elim p1 ( by 
    intro n1 h3 
    exact Exists.elim h3 ( by 
      intro h3 h4
      exact Exists.elim p2 ( by
        intro n2 h5
        exact Exists.elim h5 ( by
          intro h5 h6
          let p3:=listSplitByElem h3 h4 
          let p4:=listSplitByElem h5 h6
          have p5:L.flatten=(L.take n1).flatten++l++(L.drop (n1+1)).flatten:=calc
            L.flatten = ((L.take n1) ++ [l] ++ (L.drop (n1+1))).flatten 
                := congrArg (List.flatten) p3
            _ = ((L.take n1) ++ [l]).flatten ++ (L.drop (n1+1)).flatten
                := flatSumEqSumFlat 
            _ = (L.take n1).flatten ++ [l].flatten ++ (L.drop (n1+1)).flatten
                := by rw [flatSumEqSumFlat]
            _ = _ := by simp;rfl
          rw [p4] at p5;
          replace p4: L.flatten=
            ((List.take n1 L).flatten ++ (l.take n2)) ++ [a] ++ 
            (l.drop (n2 + 1) ++(L.drop (n1 + 1)).flatten) := by simp [p5]
          let N:=List.length (List.flatten (List.take n1 L) ++ List.take n2 l)
          have p6: N<L.flatten.length := by rw [p4];simp
          let p7:= listSplitByElemRev p4
          let p8:=(@listMemIff _ a L.flatten).mpr
          let p9:= @Exists.intro _  (fun x=> (L.flatten)[N] = a ) p6 p7
          replace p9:=@Exists.intro _ (fun m=>
            ∃(h':m<L.flatten.length),L.flatten[m]=a)  N p9
          exact p8 p9))))

end LIST

namespace List

def indexRecover {n:Nat}  (l:List (List α)) (h:n<l.flatten.length):Nat×Nat := 
  have p1: n<(l.map (fun a=>a.length)).foldl (.+.) 0:= calc
    n < l.flatten.length := h
    _ = _ :=by simp [LIST.flatLenEqSum ]
  indexRecover.f 0 (l.map (fun a=>a.length)) p1

def flatIndex {m n:Nat} (L:List (List α)) (h1:m<L.length) (_:n<L[m].length): Nat:=
  (((L.take m).map (fun a=> a.length)).foldl (.+.) 0) + n

end List

namespace LIST

lemma indexRecoverIsValid.p1 (n m:Nat) (l:List Nat) (h:n<l.foldl (.+.) 0):
List.indexRecover.f m l h=((List.indexRecover.f 0 l h).1+m,(List.indexRecover.f 0 l h).2):=by
  match l with 
  |[] => simp [List.indexRecover.f] at h
  |a::l' => 
    simp [List.indexRecover.f];
    by_cases c1:n<a
    · simp [c1]
    · simp [c1]
      apply Prod.eq_iff_fst_eq_snd_eq.mpr
      simp;push_neg at c1; simp at h
      rw [(List.indexRecover.f.p1 a l').symm] at h
      have p1 :(n-a) +a< (l'.foldl (.+.) 0) +a := calc
        _ = n := NAT.natSubtractAdd c1
        _ <a+ (l'.foldl (.+.) 0)  := h
        _ = (l'.foldl (.+.) 0) +a := by simp [add_comm]
      simp at p1
      let p2:=indexRecoverIsValid.p1 (n-a) (m+1)  l' p1
      let p3:=indexRecoverIsValid.p1 (n-a) 1  l' p1
      have p4:
        (List.indexRecover.f (m+1) l' p1).1=(List.indexRecover.f 1 l' p1).fst + m 
        := by
        rw [congrArg Prod.fst p2];
        rw [congrArg Prod.fst p3];
        simp;abel
      have p5: 
        (List.indexRecover.f (m+1) l' p1).snd=(List.indexRecover.f 1 l' p1).snd
        := by
        rw [congrArg Prod.snd p2];
        rw [congrArg Prod.snd p3];
      exact ⟨p4,p5⟩   

lemma indexRecoverIsValid.p2 {L:List (List α)} {n:Nat} (h:n<L.flatten.length):
(L.indexRecover h).1<L.length := by
  match L with 
  |[] => simp [List.flatten,List.flatten.f] at h
  |l::L' => 
    simp [List.flatten,List.flatten.f,List.indexRecover,List.indexRecover.f];
    by_cases c1:n<l.length
    · simp [c1]
    · simp [c1]
      rw [indexRecoverIsValid.p1 ] ;rw [Nat.succ_eq_one_add];
      rw [add_comm 1];simp;push_neg at c1;
      have p3 : (n-l.length)+l.length<L'.flatten.length +l.length:=calc
        _ = n :=NAT.natSubtractAdd c1
        _ < ((l::L').flatten).length :=h
        _ = ([l]++L').flatten.length := by simp 
        _ = _ := by 
            rw [flatSumEqSumFlat];
            simp [List.flatten,List.flatten.f,add_comm] 
      simp at p3
      let p4:= @indexRecoverIsValid.p2 L' _ p3 
      simp [List.indexRecover] at p4;exact p4

lemma indexRecoverIsValid.p3 {n:Nat} (l:List Nat) (h:n<l.foldl (.+.) 0):
((l.take (List.indexRecover.f 0 l h).1).foldl (.+.) 0 ≤ n)∧
(n < (l.take ((List.indexRecover.f 0 l h).1 +1)).foldl (.+.) 0) := by
  match l with 
  |[] => simp at h
  |a::l' => 
    simp [List.indexRecover.f]
    by_cases c1:n<a 
    · simp [c1];
    · simp [c1];push_neg at c1;
      rw [indexRecoverIsValid.p1];simp [(List.indexRecover.f.p1 a _).symm]
      have p1:n-a +a < (l'.foldl (.+.) 0 )+a:= calc
        n-a +a = n := NAT.natSubtractAdd c1
        _ < _ := h
        _ = a + (l'.foldl (.+.) 0 ) := by simp [(List.indexRecover.f.p1 a _).symm]
        _ = _ := by simp[add_comm]
      simp at p1 
      let p2:=indexRecoverIsValid.p3 l' p1
      let p2_1:=p2.1;let p2_2:=p2.2
      have p3:=calc
        a+ ((l'.take (List.indexRecover.f 0 l' p1).1).foldl (.+.) 0 )
          =((l'.take (List.indexRecover.f 0 l' p1).1).foldl (.+.) 0 ) +a 
              := by simp [add_comm]
        _ ≤ (n-a) +a := by apply Nat.add_le_add_right;exact p2_1
        _ = n := (NAT.natSubtractAdd c1)
      have p4:= calc
        n = (n-a) +a :=(NAT.natSubtractAdd c1).symm
        _ < ((l'.take ((List.indexRecover.f 0 l' p1).1 +1)).foldl (.+.) 0)+a 
            := by apply Nat.add_lt_add_right;exact p2_2
        _ = a + ((l'.take ((List.indexRecover.f 0 l' p1).1 +1)).foldl (.+.) 0) 
            := by simp [add_comm]
      exact ⟨ p3,p4⟩ 

lemma indexRecoverIsValid.p4 {n:Nat} (l:List Nat) (h:n<l.foldl (.+.) 0):
((l.take (List.indexRecover.f 0 l h).1).foldl (.+.) 0)+(List.indexRecover.f 0 l h).2 =n :=by
  match l with
  |[] => simp at h
  |a::l' =>
    simp [List.indexRecover.f]
    by_cases c1: n<a
    · simp [c1]
    · simp [c1];push_neg at c1
      rw [indexRecoverIsValid.p1];
      simp;rw [(List.indexRecover.f.p1 a _).symm]
      have p1:n-a +a < (l'.foldl (.+.) 0 )+a:= calc
        n-a +a = n := NAT.natSubtractAdd c1
        _ < _ := h
        _ = a + (l'.foldl (.+.) 0 ) := by simp [(List.indexRecover.f.p1 a _).symm]
        _ = _ := by simp[add_comm]
      simp at p1
      let p2:=indexRecoverIsValid.p4 l' p1
      rw [add_assoc,p2,add_comm]
      exact NAT.natSubtractAdd c1

lemma indexRecoverIsValid {L:List (List α)} {n:Nat} (h:n<L.flatten.length)
(h':(L.indexRecover h).1<L.length:=indexRecoverIsValid.p2 h):
((L.indexRecover h).1<L.length)∧((L.indexRecover h).2<L[(L.indexRecover h).1].length):=by
  have p:(L.indexRecover h).2<L[(L.indexRecover h).1].length:= by
    simp [List.indexRecover];set L2:=L.map (fun a=>a.length) with ←h1
    set l:=L[(L.indexRecover h).1] with h2;let h3:=h
    simp_rw [h1];rw [flatLenEqSum,h1] at h3
    let p1:=indexRecoverIsValid.p3 L2 h3
    let p1_1:=p1.1;let p1_2:=p1.2
    let p2:=listSplitByElem h' h2.symm
    have p3: 
      (L.take ((List.indexRecover L h).fst)++[l]).length =(List.indexRecover L h).fst + 1:= calc
      _ = (L.take ((List.indexRecover L h).fst)).length+([l]).length := List.length_append _ _
      _ = (L.take ((List.indexRecover L h).fst)).length +1 := by simp
      _ = _ := by rw [listTakeLenLeq (NAT.natLtIff.mp h').2]
    replace p4:=listTakeLeft ((L.take (List.indexRecover L h).fst)++[l]) 
        (L.drop ((List.indexRecover L h).fst+1)) p3
    rw [← p2] at p4;
    have p5: (List.indexRecover.f 0 L2 h3)= (List.indexRecover L h):=by
      simp [List.indexRecover]
    rw [← p5] at p4;
    let rec p6 (m:Nat) (j:List (List α )): 
      ((j.take m).map (fun a=> a.length)) = (j.map (fun a=> a.length)).take m :=by
      match j with 
      |[] => simp
      |a::j' =>
        match m with
        |0 => simp
        |.succ m' =>
          simp;exact p6 m' j'
    simp_rw [ h1,← p6,p4] at p1_2;simp at p1_2; simp_rw [← p6] at p1_1
    let p7:= indexRecoverIsValid.p4 L2 h3
    simp_rw [h1, ←p6] at p7
    set N:= List.foldl (fun x x_1 => x + x_1) 0 
      (List.map (fun a => List.length a) (List.take 
      (List.indexRecover.f 0 (List.map (fun a => List.length a) L) h3).fst L))
    replace p7:= calc
      N + (n-N) = n-N+N := by simp [add_comm]
      n-N+N = n :=NAT.natSubtractAdd p1_1
      n = N + (List.indexRecover.f 0 (L.map (fun a =>a.length)) h3).snd:= p7.symm
    replace p1_2 := calc
      N + (n-N) = n-N+N := by simp [add_comm]
      n-N+N = n :=NAT.natSubtractAdd p1_1
      _ < N+ L[(List.indexRecover L h).1].length := p1_2
    replace p1_2:=(add_lt_add_iff_left N).mp p1_2
    simp at p7
    exact p7 ▸ p1_2
  exact ⟨h',p⟩ 

lemma indexRecoverEqOrig {L:List (List α)} {n:Nat} (h:n<L.flatten.length)
(h1':(L.indexRecover h).1<L.length:=(indexRecoverIsValid h).left)
(h2':(L.indexRecover h).2<L[(L.indexRecover h).1].length:=(indexRecoverIsValid h).right):
L[(L.indexRecover h).1][(L.indexRecover h).2] = L.flatten[n]:= by
  let h2'':=h2'
  set L2:=L.map (fun a=>a.length) with ←h1
  set l:=L[(L.indexRecover h).1] with h2
  let p2:=listSplitByElem h1' h2.symm  
  let h3:=h;rw [flatLenEqSum] at h3 
  let p3:=indexRecoverIsValid.p4 L2 h3
  simp_rw [h1, ←indexRecoverIsValid.p6] at p3
  have p4:(( L.take (L.indexRecover h).1).map (fun a=>a.length)).foldl (.+.) 0
    = ( L.take (L.indexRecover h).1).flatten.length := by rw [flatLenEqSum]
  simp [List.indexRecover] at p4 h2';rw [p4] at p3;
  set m:=List.indexRecover.f 0 (L.map (fun a => List.length a) ) 
    (_ : n < List.foldl (.+.) 0 (L.map (fun a => List.length a) ))
  set a:=l[m.2] with h4
  let p5:= listSplitByElem _ h4.symm
  replace p2:=congrArg List.flatten p2
  rw [flatSumEqSumFlat,flatSumEqSumFlat] at p2;
  have p7:[l].flatten=l := by simp [List.flatten,List.flatten.f]
  rw [p7] at p2;rw [p5] at p2;
  replace p7 :
      (List.take (List.indexRecover L h).1 L).flatten ++ 
      ((l.take m.2)++[a]++(l.drop (m.2 +1))) ++
      (L.drop ((List.indexRecover L h).1 + 1) ).flatten
      = ((List.take (List.indexRecover L h).1 L).flatten ++ 
      (l.take m.2))++[a]++((l.drop (m.2 +1)) ++
        (L.drop ((List.indexRecover L h).1 + 1) ).flatten) := by simp
  let p9:=listSplitByElemRev p7
  simp_rw [← h2];
  set B:=(List.take (List.indexRecover L h).1 L).flatten ++ 
      ((l.take m.2)++[a]++(l.drop (m.2 +1))) ++
      (L.drop ((List.indexRecover L h).1 + 1) ).flatten 
  have p7':n<B.length := by
    let p7'':= congrArg List.length p2
    rw [p7''.symm];exact h
  have p10:B[List.length (List.flatten (List.take 
    (List.indexRecover L h).fst L) ++ List.take m.snd l)] =a :=p9
  have p11:(l.take m.2).length=m.2 :=listTakeLenLeq  (NAT.natLtIff.mp h2'').right
  have p12: List.length (List.flatten (List.take 
    (List.indexRecover L h).fst L) ++ List.take m.snd l) =n := calc
      List.length (List.flatten (List.take 
      (List.indexRecover L h).fst L) ++ List.take m.snd l) 
        = (L.take (List.indexRecover L h).1).flatten.length + (l.take m.2).length
            := by simp
      _ = (L.take (List.indexRecover L h).1).flatten.length +m.2 := by rw [p11] 
      _ = _ := p3  
  have p11: B[List.length (List.flatten (List.take 
    (List.indexRecover L h).fst L) ++ List.take m.snd l)] = B[n] := by simp_rw [p12]
  replace p11:= p10 ▸ p11
  have p13:l[(List.indexRecover L h).snd] = a := rfl
  rw [p13,p11];simp_rw [p2]

lemma indexRecoverInj {L:List (List α)} {n m:Nat} 
(h1:n<L.flatten.length) (h2:m<L.flatten.length) (h3:L.indexRecover h1 = L.indexRecover h2)
:n = m := by
  simp [List.indexRecover] at h3
  set L2:=L.map (fun a=>a.length) with H
  simp_rw [H.symm] at h3
  have p1:n<L2.foldl (.+.) 0:=by
    rw [←flatLenEqSum];exact h1
  have p2:m<L2.foldl (.+.) 0:=by
    rw [←flatLenEqSum];exact h2
  let p3:=indexRecoverIsValid.p4 L2 p1
  let p4:=indexRecoverIsValid.p4 L2 p2
  rw [p3.symm,p4.symm,h3]

lemma flatIndexIsValid {m n:ℕ}(L:List (List α))(h1:m<List.length L)(h2:n<List.length L[m]):
L.flatIndex h1 h2 < L.flatten.length := by
  set l:=L[m] with ←h3
  set a:=L[m][n]  with ←h4
  let p1:=listSplitByElem h1 h3
  let p2:=listSplitByElem h2 h4
  replace p1:=congrArg List.flatten p1
  rw [flatSumEqSumFlat,flatSumEqSumFlat] at p1
  have p3:[l].flatten = l := by simp [List.flatten,List.flatten.f]
  replace p1:= (p3 ▸ p1);replace p1:= p2 ▸ p1
  have p4: (l.take n).length=n := listTakeLenLeq (NAT.natLtIff.mp h2).right
  have p5:(List.take m L).flatten++((l.take n)++[a]++(l.drop (n + 1)))++(L.drop (m + 1)).flatten 
    =((List.take m L).flatten++(l.take n))++[a]++((l.drop (n + 1))++(L.drop (m + 1)).flatten)
      := by simp
  replace p1:=p5 ▸ p1
  set k:=L.flatIndex h1 h2 
  have p6:(((L.take m).map (fun a=> a.length)).foldl (.+.) 0) + n =k := rfl
  rw [←flatLenEqSum] at p6
  replace p6:= p4.symm ▸ p6
  have p7: List.length ((List.take m L).flatten ++ l.take n) < L.flatten.length := by
    rw [p1];simp
  replace p7:=calc
    (List.take m L).flatten.length+(l.take n).length 
    = ((List.take m L).flatten ++ l.take n).length := by simp
    _ < L.flatten.length :=p7
  replace p7:=p6 ▸ p7;exact p7

lemma flatIndexEqFlat {m n:ℕ}(L:List (List α))(h1:m<List.length L)(h2:n<List.length L[m])
(h':=flatIndexIsValid L h1 h2):L[m][n]=L.flatten[L.flatIndex h1 h2] := by
  set l:=L[m] with ←h3
  set a:=L[m][n]  with ←h4
  let p1:=listSplitByElem h1 h3
  let p2:=listSplitByElem h2 h4
  replace p1:=congrArg List.flatten p1
  rw [flatSumEqSumFlat,flatSumEqSumFlat] at p1
  have p3:[l].flatten = l := by simp [List.flatten,List.flatten.f]
  replace p1:= (p3 ▸ p1);replace p1:= p2 ▸ p1
  have p4: (l.take n).length=n := listTakeLenLeq (NAT.natLtIff.mp h2).right
  have p5:(List.take m L).flatten++((l.take n)++[a]++(l.drop (n + 1)))++(L.drop (m + 1)).flatten 
    =((List.take m L).flatten++(l.take n))++[a]++((l.drop (n + 1))++(L.drop (m + 1)).flatten)
      := by simp
  replace p1:=p5 ▸ p1
  let p1':=listSplitByElemRev p1
  set k:=L.flatIndex h1 h2 
  have p6:(((L.take m).map (fun a=> a.length)).foldl (.+.) 0) + n =k := rfl
  rw [←flatLenEqSum] at p6
  replace p6:= p4.symm ▸ p6
  replace p7:
    (List.take m L).flatten.length+(l.take n).length 
    = ((List.take m L).flatten ++ l.take n).length := by simp
  replace p6:=p7 ▸ p6
  have p8:L.flatten[k]=a := by simp_rw [p6.symm];exact p1'
  exact p8.symm

end LIST

namespace FINSET

def finsetRange:=Finset.range

def finSubsetIff:=@ Finset.subset_iff

def finsetSubsetCard:=@Finset.card_le_of_subset

def finsetEmptyIff  {s : Finset α}: s=∅ ↔ Finset.card s =0 := 
  let h:=@Finset.card_eq_zero α s
  ⟨h.mpr, h.mp ⟩ 

def finsetNonEmptyIff {s : Finset α}: s.Nonempty ↔ s.card>0 :=
  let h:=@Finset.card_pos α s
  {mp:=h.mpr, mpr:= h.mp} 

lemma finsetNonEmptyMpr {s : Finset α} : s≠∅ -> s.Nonempty := by
  intro h
  exact Finset.nonempty_of_ne_empty h

@[simp]
lemma finsetNeqEmptyIff {s : Finset α}: (s≠∅)↔ s.Nonempty:=
  ⟨Finset.nonempty_iff_ne_empty.mpr,
    Finset.nonempty_iff_ne_empty.mp⟩ 

def finSubsetUnion [DecidableEq α]{s:Finset α}{t:Finset α}{u:Finset α} 
  (hs :s⊆u) (ht: t⊆u) :=Finset.union_subset hs ht

lemma finsetCardEqListLength {s:Finset α}:s.card = s.toList.length :=by simp

lemma finsetUnionOfDisjoint [ DecidableEq α] (l:List (Finset α)) (s:Finset α) 
(h1:∀{s1},(s1∈l)->s1⊆s) 
(h2:∀{i j:Nat},(pIdx1:i<l.length)->(pIdx2:j<l.length)->(i≠j)->(l[i] ∩ l[j] = ∅ ))
:((l.foldr (.∪.) ∅ )⊆s)∧
((l.foldr (.∪.) ∅ ).card = (l.map (Finset.card .)).foldr (.+.) 0) ∧ 
( ∀ {a:α}, a∈(l.foldr (.∪.) ∅ ) ↔ ∃ si∈l,a∈si)  :=by
  let rec aux (l':List (Finset α)) 
    (h1':∀{s1},(s1∈l')->s1⊆s) 
    (h2':∀{i j:Nat},(pIdx1':i<l'.length)->(pIdx2':j<l'.length)->(i≠j)->(l'[i] ∩ l'[j] = ∅ ))
    : ((l'.foldr (.∪.) ∅ )⊆s)∧
      ((l'.foldr (.∪.) ∅ ).card = (l'.map (Finset.card .)).foldr (.+.) 0) ∧
      ( ∀ {a:α}, a∈(l'.foldr (.∪.) ∅ ) ↔ ∃ si∈l',a∈si)
    := by
    set L:=l' with H
    match l' with
    |[] => simp [H]
    |sn::l''=> 
      have h1'': ∀{s1},(s1∈l'')->s1⊆s := by
        intro s1 p1;rw [H] at h1'
        exact (h1' (by simp [p1]))
      have h2'': 
        ∀{i j:Nat},(pIdx1':i<l''.length)->(pIdx2':j<l''.length)->(i≠j)->(l''[i] ∩ l''[j] = ∅ ):=by
        intro i j p1 p2 p3 
        have pIdx1'':i+1<L.length:= by rw [H];simp [Nat.add_lt_add_right p1 1]
        have pIdx2'':j+1<L.length:= by rw [H];simp [Nat.add_lt_add_right p2 1]
        have p4:l''[i] = L[i+1] := by simp [H]
        have p5:l''[j] = L[j+1] := by simp [H]
        have p6: i+1≠j+1:= by simp [p3]
        replace h2':= h2' pIdx1'' pIdx2'' p6;rw [←p4,←p5] at h2'
        exact h2'
      let Hinduct:=aux l'' h1'' h2''
      let p1:=Hinduct.1;let p2:=Hinduct.2.1;
      let p3:(∀ {a:α}, a∈(l''.foldr (.∪.) ∅ ) ↔ ∃ si∈l'',a∈si):=Hinduct.2.2
      have r1: (L.foldr (.∪.) ∅ ) ⊆s:= by
        rw [H];simp
        have p4: sn∈L:=by rw [H];simp
        replace p4:=h1' p4
        exact (Finset.union_subset p4 p1)
      have r2: (L.foldr (.∪.) ∅).card = (L.map (Finset.card .)).foldr (.+.) 0:= by 
        rw [H];simp
        have p4:∀x:α,x∈(l''.foldr (.∪.) ∅ ) -> x∉sn:= by
          intro x p5;
          let p6:=(p3.mp p5)
          have p7:∀si, si∈l'' ∧ x∈si -> x∉sn := by
            intro si p8
            have p9: ∃ s t, l'' = s++si::t:=LIST.listMemSplit p8.1
            have p10: ∀ s t, l'' = s++si::t -> x∉sn := by
              intro u v p15
              have p11:L=[sn]++u++[si]++v:= by simp [H,p15]
              have p14:=LIST.listSplitByElemRev p11
              have p12':0<L.length :=by simp [H]
              have p12: L[0]=sn:= by simp [H]
              have p13:List.length ([sn] ++ u)≠ 0:= by simp
              have p13':([sn]++u).length<L.length
              :=  LIST.listSplitByElemRev.f1 p11
              replace p11:=h2' p13' p12' p13
              rw [p12,p14] at p11
              by_contra p16
              replace p16:x∈ si ∩ sn :=  Finset.mem_inter.mpr ⟨p8.2,p16⟩ 
              rw [p11] at p16
              simp at p16
            replace p10:∀ s,(∃ t, l'' = s++si::t) -> x∉sn := by
              intro s p11
              exact Exists.elim p11 (p10 s)
            exact Exists.elim p9 p10
          exact Exists.elim p6 p7
        replace p4:=Finset.disjoint_left.mpr p4
        rw [Finset.union_comm];simp[p4,p2,add_comm]
      have r3:∀ {a : α}, a ∈ L.foldr (.∪.) ∅ ↔ ∃ si, si ∈ L ∧ a ∈ si:= by
        rw [H];intro a;
        have mp:a∈ (sn::l'').foldr (.∪.) ∅ -> ∃ si, si∈(sn::l'') ∧ a∈si :=by 
          intro p4;simp at p4
          cases' p4 with p4_1 p4_2
          · exact ⟨sn,by simp [p4_1] ⟩ 
          · let p5:= p3.mp p4_2
            have p6: ∀si, (si∈l'' ∧ a∈si )-> ∃si, (si∈sn::l'' ∧ a∈si ) := by
              intro si p7
              exact ⟨si,⟨by simp [p7.1] ,p7.2⟩ ⟩ 
            exact Exists.elim p5 p6
        have mpr: (∃ si, si∈(sn::l'') ∧ a∈si )->a∈ (sn::l'').foldr (.∪.) ∅ := by
          intro p4;
          have p5:∀ si, (si∈(sn::l'') ∧ a∈si)-> a∈ (sn::l'').foldr (.∪.) ∅ := by
            intro si p6
            let p7:= p6.1;simp at p7
            cases' p7 with p7_1 p7_2
            · simp;rw [← p7_1];exact Or.inl p6.2
            · simp;exact Or.inr (p3.mpr ⟨si,⟨p7_2,p6.2 ⟩⟩ )
          exact Exists.elim p4 p5
        exact ⟨mp,mpr ⟩ 
      exact ⟨r1,r2,r3 ⟩ 
  exact aux l h1 h2 

lemma finsetCardUnionAddCardInter [DecidableEq α] (s t:Finset α):
(s ∪ t).card + (s ∩ t).card = s.card + t.card:=Finset.card_union_add_card_inter _ _

@[simp]
lemma finsetToListNodup  (s:Finset α) :s.toList.Nodup:= by 
  let p1:=s.nodup
  have p2:s.toList = s.val.toList:= by simp [Finset.toList]
  let l:=s.val.toList
  have p3:s.val=↑l:= by simp
  rw [p2];rw [p3] at p1
  exact Multiset.coe_nodup.mp p1

lemma finsetSdiffCard {s t:Finset α}[DecidableEq α](h :s⊆t):
(t \ s).card = t.card - s.card
:=Finset.card_sdiff h

lemma finsetLeSdiffCard [DecidableEq α] (s t : Finset α) :
t.card - s.card ≤ (t \ s).card:=Finset.le_card_sdiff s t

lemma finsetSdiffMemIff  [DecidableEq α] {s t:Finset α} {a : α} :
a ∈ s \ t ↔ a ∈ s ∧ a ∉ t :=Finset.mem_sdiff

lemma finsetInterMemIff [DecidableEq α] {a : α} {s t : Finset α} :
a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t :=Finset.mem_inter

lemma finsetUnionMemIff  [DecidableEq α] {a : α} {s t : Finset α} :
a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t :=Finset.mem_union

lemma finsetMemToListIff {a : α} {s : Finset α} :
a ∈ s.toList ↔ a ∈ s :=Finset.mem_toList

end FINSET

namespace FUNCTION 

open SET

abbrev FUNC  (s1:Set α) (s2:Set γ): Type max u_1 u_2
:= (↑ s1) -> (↑ s2)

@[simp]
def conven1 {s:Set α} (a:s) :(a:α )∈s := a.prop

end FUNCTION


open SET

namespace toListSubtype

structure ListSubtype' (l:List α ) where
  val:α
  property:val∈l

def aux: {k:Nat}->(l l1:List α)->(h:l1=l.drop k)->List (ListSubtype' l):=by
  intro k l l1 h
  set L:=l1 with H
  match l1 with
  |[] => exact []
  |a::l1' =>
    have p1:l1'=L.drop 1:= by simp [H]
    replace p1: l1'= l.drop (k+1):= by calc
      l1' =  L.drop 1 := p1
      _ = (l.drop k).drop 1:=by rw [h]
      _ = l.drop (1+ k ) := LIST.listDropDrop _ _ _
      _ = l.drop (k+1):= by simp[Nat.add_comm]
    have p2:a∈ L:= by simp [H]
    have p3:k≤l.length:= by
      by_contra hc;push_neg at hc
      have p4:l.length+1≤ k:= LT.lt.nat_succ_le hc
      have p5:l.drop k =[] := by calc
        l.drop k = l.drop (k- (l.length+1) +(l.length+1))
            := by simp [NAT.natSubtractAdd p4]
        _ = (l.drop (l.length+1)).drop (k- (l.length+1))
            := (LIST.listDropDrop (k- (l.length+1)) (l.length+1) l).symm
        _ = (l.drop (1+ l.length)).drop (k- (l.length+1)) := by rw [Nat.add_comm]
        _ = ((l.drop l.length).drop 1).drop (k- (l.length+1))
            := by rw [LIST.listDropDrop 1 l.length l]
        _ = ([].drop 1).drop (k- (l.length+1)) := by simp
        _ = [] := by simp
      simp_all
    let p4:=LIST.listSplit p3
    have p5:a∈ List.drop k l := by simp [h] at p2;exact p2 
    replace p5:= 
      (@LIST.listMemOfSumIff _ a (List.take k l) (List.drop k l)).mpr
        (Or.inr p5)
    rw [← p4] at p5
    exact ⟨a,p5⟩::(aux _ _ p1) 

def f1 {a:α}{l l':List α}: (a::l' = l.drop k)->(a∈l):= by 
  intro  p2;
  have p1:a∈a::l':= by simp
  rw [p2] at p1
  have p3:k≤l.length:= by
    by_contra hc;push_neg at hc
    have p4:l.length+1≤ k:= LT.lt.nat_succ_le hc
    have p5:l.drop k =[] := by calc
      l.drop k = l.drop (k- (l.length+1) +(l.length+1))
          := by simp [NAT.natSubtractAdd p4]
      _ = (l.drop (l.length+1)).drop (k- (l.length+1))
          := (LIST.listDropDrop (k- (l.length+1)) (l.length+1) l).symm
      _ = (l.drop (1+ l.length)).drop (k- (l.length+1)) := by rw [Nat.add_comm]
      _ = ((l.drop l.length).drop 1).drop (k- (l.length+1))
          := by rw [LIST.listDropDrop 1 l.length l]
      _ = ([].drop 1).drop (k- (l.length+1)) := by simp
      _ = [] := by simp
    simp_all
  let p4:=LIST.listSplit p3
  rw [p4];
  exact (@LIST.listMemOfSumIff _ a (List.take k l) (List.drop k l)).mpr
        (Or.inr p1)

def f2 {a:α}{l l':List α} {k:Nat}: (a::l' = l.drop k)->(l'=l.drop (k+1)):= by
  intro p1
  calc
    l' = ( a :: l').drop 1 := by simp
    _ = (l.drop k).drop 1 := by rw [← p1]
    _ = l.drop (k+1):= by simp [Nat.add_comm]

lemma auxInduction {l l':List α} {k:Nat}{a:α} (h:(a::l')=l.drop k): 
aux l (a::l')  h = ⟨a,f1 h ⟩ ::(aux l l' (f2 h) ):= by rfl

lemma auxLenEq {k:Nat} (l l1:List α) (h:l1=l.drop k): 
l1.length = (aux l l1 h).length:=by 
  set L:=l1 with H
  match l1 with 
  |[] =>simp [aux]
  |a::l1' =>  
    let p1:=@auxInduction _ (l) (l1') k a h
    rw [p1];simp;
    let p2:=f2 h
    exact auxLenEq l l1' p2

def f3 (l l1:List α) (h1:l1=l.drop k)(h2:n<l1.length):k +n<l.length:= by
  set a:=l1[n] with ← H
  let p1:=LIST.listSplitByElem h2 H
  have p2:l1.length≤l.length:=by
    rw [h1];
    exact LIST.listDropLenLeqOrig
  by_cases c:k≤l.length
  · let p3:=LIST.listSplit c
    rw [← h1] at p3;rw [p1] at p3
    let p4:=LIST.listTakeLenLeq c 
    have h2':n≤l1.length
      := (NAT.natLtIff.mp h2).2
    let p5:=LIST.listTakeLenLeq h2'
    let p6:=(List.length_append ((l1.take n)++ [a]) (l1.drop (n+1)))
    calc
      k+n < k+n+1:= by simp
      _ = (l.take k).length + (l1.take n).length +1
          := by simp [p4,c,p5,h2']
      _ ≤ (l.take k).length + (l1.take n).length +[a].length + (l1.drop (n+1)).length
          := by simp
      _ = (l.take k).length + ((l1.take n).length +[a].length) + (l1.drop (n+1)).length 
          := by abel
      _ = (l.take k).length + (((l1.take n)++[a]).length) + (l1.drop (n+1)).length
          := by simp
      _ = (l.take k).length + ((((l1.take n)++[a]).length) + (l1.drop (n+1)).length)
          := by  simp [Nat.add_assoc]
      _ = (l.take k).length + ((l1.take n)++ [a] ++ (l1.drop (n+1))).length
          := by rw [← p6]
      _ = (l.take k++((l1.take n)++[a]++(l1.drop (n+1)))).length := by simp
      _ = _ := by rw [← p3]
  · push_neg at c
    let p3:=(NAT.natLtIff.mp c).2
    replace p3: k- l.length + l.length =k :=NAT.natSubtractAdd p3
    have p4: l1=[]:=calc
      l1 = l.drop k :=h1
      _ = l.drop (k- l.length + l.length):= by simp [ p3]
      _ = (l.drop (l.length)).drop (k- l.length) 
          :=(LIST.listDropDrop (k- l.length) l.length _ ).symm
      _ = [] := by simp
    rw [p4] at h2;simp at h2

lemma auxEqOrig {k n:Nat} (l l1:List α) (h1:l1=l.drop k)
(h2:n<l1.length) (h3:n<(aux l l1 h1).length) (h4:k +n<l.length:=f3 l l1 h1 h2 )
: ((aux l l1 h1)[n]).val = l[k +n] := by 
  set L:=l1 with H 
  match l1 with
  |[]=>simp [aux] at h3
  |a::l1'=>
    let p1:=@auxInduction _ (l) (l1') k a h1
    match n with
    |0 =>
      simp_rw [p1];simp
      have p2:k≤l.length:=(NAT.natLtIff.mp h4).2
      let p3:=LIST.listSplit p2
      rw [← h1] at p3
      set M:=List.take k l with I
      let p4:=LIST.listTakeLenLeq p2
      rw [← I] at p4
      have p5:M ++ a :: l1' = M++[a]++l1':= by simp
      rw [p5] at p3
      replace p5:=LIST.listSplitByElemRev p3
      simp_rw [p4] at p5;exact p5.symm
    |.succ n' =>
      simp_rw [p1];
      have p2: l1' = List.drop (k + 1) l:= calc
        l1' = (a :: l1').drop 1 := by simp
        _ = (l.drop k).drop 1:= by rw [h1]
        _ = l.drop (k+1):= by simp [LIST.listDropDrop,Nat.add_comm]
      have p3:n'<l1'.length:= by
        simp at h2;exact Nat.lt_of_succ_lt_succ h2
      have p4:n'<(aux l l1' p2).length:=by
        let p5:=auxLenEq l l1' p2
        rw [← p5];exact p3
      let p5:= auxEqOrig l l1' p2 p3 p4
      let p6:k + 1 + n' = k+n'.succ:= by calc
        _ = k + ( n'+1 ) := by abel
        _ = k+n'.succ := by simp
      have p7 : k + 1 + n'<l.length := calc
        k + 1 + n' = k + ( n'.succ ):= p6
        _ <l.length :=h4
      have p8:
        (aux l l1' p2)[n'].val = l[k + n'.succ] := by calc
          _ = l[k + 1 + n'] := p5
          _ = l[k + n'.succ]:= by simp_rw [p6]
      rw [← p8] ;simp

end toListSubtype

structure ListSubtype (l:List α )  where
  val:α 
  property:val∈l
  n:Nat
  p2:n<l.length
  p3:l[n]=val

namespace List

def  toSubtype.aux (l:List α): {k:Nat}->{l1:List α }
->(h:l1=l.drop k )->(List (ListSubtype l)):=by
  intro k l1 h  
  match l1 with
  |[] => exact []
  |a::l1' => 
    have p1: 0<(a::l1').length:= by simp
    have p2: 0< (toListSubtype.aux l (a::l1') h).length:= by 
      let p3:=toListSubtype.auxLenEq l (a::l1') h
      exact p3 ▸ p1
    let p3:= toListSubtype.auxEqOrig l (a::l1') h p1 p2
    simp at p3
    let p5:=toListSubtype.f3 _ _ h p1
    simp at p5
    have p6:l1'=l.drop (k+1):=calc
      l1' = (a::l1').drop 1 := by simp
      _ = (l.drop k).drop 1 := by rw [h]
      _ = _ := by simp [Nat.add_comm]
    have p7: a∈l.drop k := by rw [h.symm];simp
    replace p7: a∈l:= List.mem_of_mem_drop p7
    exact {val:=a,property:=p7,n:=k,p2:=p5,p3:=p3.symm }::(aux l p6) 

def toSubtype: (l:List α)->(List (ListSubtype l)):=
  fun l =>
  have p1:l=l.drop 0:= by simp
  List.toSubtype.aux l  p1

end List

namespace LIST

lemma toSubtype.aux.lenEqOrig: {l l1: List α}->{k:Nat}->(h:l1=l.drop k )
->((List.toSubtype.aux l h).length=l1.length ):= by
  intro l l1
  match l1 with 
  |[] => simp [List.toSubtype.aux]
  |a::l1' =>
    intro k h
    simp [List.toSubtype.aux]
    have p1:l1'=l.drop (k+1):= calc
      l1' = (a::l1').drop 1 := by simp
      _ = (l.drop k).drop 1 := by rw [h]
      _ = l.drop (1+k) := LIST.listDropDrop _ _ _
      _ = l.drop (k+1) := by simp [Nat.add_comm]
    exact aux.lenEqOrig p1

lemma toSubtypeLenEqOrig: (l:List α)->((l.toSubtype).length=l.length):= by
  intro l 
  match l with
  |[] =>
    simp [List.toSubtype,List.toSubtype.aux]
  |a::l' =>
    simp [List.toSubtype] 
    simp [List.toSubtype.aux]
    have p1: (a::l').drop 1 = l' := by simp
    exact toSubtype.aux.lenEqOrig p1.symm

lemma toSubtype.aux.auxEqOrig {k n:Nat} {l l1:List α} (h1:l1=l.drop k)
(h2:n<l1.length) (h3:n<(List.toSubtype.aux l h1).length:=toSubtype.aux.lenEqOrig h1 ▸ h2) 
(h4:k +n<l.length:=toListSubtype.f3 l l1 h1 h2 )
: ((List.toSubtype.aux l h1)[n]).val = l[k +n] := by 
  set L:=l1 with H 
  match l1 with
  |[]=>
    simp [List.toSubtype.aux] at h3
    by_contra
    exact  h3
  |a::l1'=>
    match n with
    |0 =>
      have p2:k≤l.length:=(NAT.natLtIff.mp h4).2
      let p3:=LIST.listSplit p2
      rw [← h1] at p3
      set M:=List.take k l with I
      let p4:=LIST.listTakeLenLeq p2
      rw [← I] at p4
      have p5:M ++ a :: l1' = M++[a]++l1':= by simp
      rw [p5] at p3
      replace p5:=LIST.listSplitByElemRev p3
      simp_rw [p4] at p5;exact p5.symm
    |.succ n' =>
      have p2: l1' = List.drop (k + 1) l:= calc
        l1' = (a :: l1').drop 1 := by simp
        _ = (l.drop k).drop 1:= by rw [h1]
        _ = l.drop (k+1):= by simp [LIST.listDropDrop,Nat.add_comm]
      have p3:n'<l1'.length:= by
        simp at h2;exact Nat.lt_of_succ_lt_succ h2
      have p4:n'<(List.toSubtype.aux l  p2).length:=by
        let p5:= toSubtype.aux.lenEqOrig p2
        rw [p5];exact p3
      let p5:= auxEqOrig p2 p3 p4
      let p6:k + 1 + n' = k+n'.succ:= by calc
        _ = k + ( n'+1 ) := by abel
        _ = k+n'.succ := by simp
      have p7 : k + 1 + n'<l.length := calc
        k + 1 + n' = k + ( n'.succ ):= p6
        _ <l.length :=h4
      have p8:
        (List.toSubtype.aux  l p2)[n'].val = l[k + n'.succ] := by calc
          _ = l[k + 1 + n'] := p5
          _ = l[k + n'.succ]:= by simp_rw [p6]
      rw [← p8] ;simp

lemma  toSubtypeNEqOrigN (l:List α)(h:n<l.length)
(h':n<l.toSubtype.length:=(toSubtypeLenEqOrig l )▸h):l.toSubtype[n].val=l[n] :=by
  have p1:=calc
    n < l.length := h
    _ = (l.drop 0).length := by simp
  let p2:=toSubtype.aux.auxEqOrig (by simp:l=l.drop 0) p1
  simp [List.toSubtype]
  simp at p2;exact p2

variable (l:List α )
instance : CoeDep (ListSubtype l) e α where
  coe:=e.val


end LIST

namespace Finset

def toSubtype.f {s:Finset α}:(ListSubtype (s.toList))->(Subtype s.toSet):=
    fun e=>⟨e.val,Finset.mem_toList.mp e.property ⟩ 

noncomputable def toSubtype: (s:Finset α)->Finset (Subtype s.toSet) := by
  intro s
  let l1:=s.toList.toSubtype
  let l2:=l1.map toSubtype.f
  have p1:∀ {i j:ℕ}(h1:i<l2.length)(h2:j<l2.length),i≠j→l2[i]≠l2[j]:= by
    intro i j h1 h2 h3
    have p2:l1.length=l2.length:= by simp
    let p3:= p2.symm ▸ h1
    let p4:= p2.symm ▸ h2
    have p3':l2[i]=toSubtype.f l1[i] := by simp
    have p4':l2[j]=toSubtype.f l1[j] := by simp
    rw [p3',p4']
    by_contra hc 
    have p5 {e1 e2:(ListSubtype (s.toList))}:
      (toSubtype.f e1 =toSubtype.f e2)->(e1.val)=(e2.val):=by
      simp [toSubtype.f]
    replace p5:=p5 hc
    replace p3:=calc
      i < List.length l1 :=p3   
      _ = s.toList.length := by simp [(LIST.toSubtypeLenEqOrig s.toList)]
    replace p4:=calc
      j < List.length l1 :=p4
      _ = s.toList.length := by simp [(LIST.toSubtypeLenEqOrig s.toList)]
    rw [LIST.toSubtypeNEqOrigN s.toList p3,(LIST.toSubtypeNEqOrigN s.toList p4)] at p5
    replace hc:∀ {i j:ℕ}(h1:i<s.toList.length)(h2:j<s.toList.length),
    i ≠ j → (toList s)[i] ≠ (toList s)[j] := 
      (LIST.listNodupIff ).mp (by simp:s.toList.Nodup )
    replace hc:=LOGIC.contraposeH (hc p3 p4)
    push_neg at hc
    exact h3 (hc p5) 
  replace p1:=(@LIST.listNodupIff _).mpr p1
  exact ⟨l2,p1⟩ 

end Finset

namespace FINSET

@[simp]
lemma toSubtypeCardEqOrig: (s:Finset α)-> s.toSubtype.card = s.card := by
  intro s
  simp [Finset.toSubtype]
  have p2:s.toList.toSubtype.length=s.toList.length:=LIST.toSubtypeLenEqOrig s.toList
  simp_all

lemma toSubtypeMemMpr (s:Finset α) {a:α}: (h:a∈s)->⟨a,h⟩∈s.toSubtype:=by 
  intro h
  have p1: a∈s.toList := by simp [h]
  let p2:=LIST.listMemSplit p1
  exact Exists.elim p2 (by
    intro l1 h1 
    exact Exists.elim h1 (by
      intro l2 h2
      have p3:s.toList = l1 ++ [a] ++l2 := by simp [h2]
      replace p3:=LIST.listSplitByElemRev p3
      have p3':=LIST.toSubtypeNEqOrigN s.toList (by simp_all:l1.length<s.toList.length)
      replace p3:=p3'.symm ▸ p3
      have p4: l1.length< s.toList.toSubtype.length  := calc
        l1.length < s.toList.length := by simp_all
        _ = s.toList.toSubtype.length := (LIST.toSubtypeLenEqOrig s.toList).symm
      have p5: l1.length < (s.toList.toSubtype.map Finset.toSubtype.f).length := by simp [p4]
      have p6: (s.toList.toSubtype.map Finset.toSubtype.f)[l1.length] 
        = Finset.toSubtype.f s.toList.toSubtype[l1.length]:= by simp
      have p7:Finset.toSubtype.f (s.toList.toSubtype)[List.length l1]=⟨a,h⟩ := calc
        Finset.toSubtype.f (s.toList.toSubtype)[l1.length] = 
              ⟨(s.toList.toSubtype)[List.length l1].val ,
                Finset.mem_toList.mp (s.toList.toSubtype)[l1.length].property ⟩ 
                := by simp [Finset.toSubtype.f]
        _ = ⟨a,h⟩ := by simp_rw [p3] 
      replace p7:=p6.symm ▸ p7
      replace p6:l1.length<(s.toList.toSubtype.map Finset.toSubtype.f).length := by simp_all
      let p8:=LIST.listGetIsMem p6
      replace p8:=p7 ▸ p8
      have p9 {x:Subtype s.toSet}:
        (h3:x∈ s.toList.toSubtype.map Finset.toSubtype.f)->(x∈(s.toSubtype)):=by
        intro h3
        have p10:s.toSubtype.val= ↑(s.toList.toSubtype.map Finset.toSubtype.f)
          := by simp [Finset.toSubtype]
        replace h3:x∈((s.toList.toSubtype.map Finset.toSubtype.f):Multiset _):= by simp_all
        replace p10:=p10.symm ▸ h3
        simp_all
      exact p9 p8
      )
    )
    
lemma toSubtypeMemMpr' (s:Finset α) (a:Subtype s.toSet): a∈s.toSubtype:=by 
  let p1:=toSubtypeMemMpr s a.property
  have p2:⟨a,a.property ⟩ = a := by rfl 
  rw [p2] at p1
  exact p1

end FINSET

namespace REAL

lemma leFlip {x y:Real} (h:x≤y): (-y≤-x) := by simp;exact h

lemma ltFlip {x y:Real} (h:x<y): ((-y)<(-x)) := by simp;exact h

lemma leAddLt {w x y z:Real} (h1:x≤y) (h2:w<z) : ((x+w)<(y+z)) := calc
  x+w ≤ y+w := by simp [h1]
  _ < y+z := by simp [h2]

lemma leAddLe {w x y z:Real} (h1:x≤y) (h2:w≤z) : ((x+w)≤(y+z)) := calc
  x+w ≤ y+w := by simp [h1]
   _ ≤  y+z := by simp [h2]

lemma addLeAddMpr {x y:Real} (h:x≤y) (z:Real) : x+z ≤ y+z := by simp [h]

lemma addLtAddMpr {x y:Real} (h:x<y) (z:Real) : x+z < y+z := by simp [h]

lemma mulNonNegLeMulNonMegMpr {x y z:Real} (h1:x≤y) (h2:0≤z) : x*z ≤ y*z := by 
  by_cases hc: 0≤x 
  · have p2: 0≤z := h2
    have p1 := calc 
      0 ≤ x := hc
      _ ≤ y := h1
    have p3:z≤z := by simp
    exact mul_le_mul h1 p3 p2 p1
  · push_neg at hc
    replace hc: 0< (-x) := by simp [hc]
    let p1:= leFlip h1
    let p2:z≤z := by simp
    let p3:=mul_le_mul p1 p2 h2 hc.le
    have p4 :  -(y*z) ≤  -(x*z )  := calc 
      _ = -y * z := by simp
      _ ≤ -x * z :=p3
      _ = _  := by simp
    replace p4:=leFlip p4
    simp at p4;exact p4

lemma mulPosLtMulPosMpr {x y z:Real} (h1:x<y) (h2:0<z) : x*z < y*z := by
  have p1:x*z ≠ y*z := by
    by_contra hc
    simp at hc
    cases' hc with H1 H2
    · exact absurd H1 h1.ne
    · exact absurd H2 (h2.ne).symm
  let p2:=mulNonNegLeMulNonMegMpr h1.le h2.le
  exact p2.lt_of_ne p1
      
lemma mulNegLeMulNegMpr {x y z:Real} (h1:x≤y) (h2:z≤0) : y*z≤x*z  := by 
  have p1:0≤ (-z) := by simp [h2]
  let p2:= leFlip ( mulNonNegLeMulNonMegMpr  h1 p1)
  simp at p2;exact p2
    
lemma mulNegLtMulNegMpr {x y z:Real} (h1:x<y) (h2:z<0) : y*z<x*z  := by 
  have p1:x*z ≠ y*z := by
    by_contra hc
    simp at hc
    cases' hc with H1 H2
    · exact absurd H1 h1.ne
    · exact absurd H2 (h2.ne)
  let p2:=mulNegLeMulNegMpr h1.le h2.le
  exact p2.lt_of_ne p1.symm

lemma invLeInvMpr {x y:Real} (h1:0<x) (h2:x≤y): 1/y ≤ 1/x :=by
  have p1 := calc
    _ < _ := h1
    _ ≤ _ :=h2
  simp
  exact (inv_le_inv p1 h1).mpr h2

lemma invNegEqNegInv {x:Real}: 1/(-x) = - (1/x) := by 
  simp
  exact inv_neg

lemma posInvIsPos {x:Real} (h:0<x):0<1/x := by simp [h]
  
end REAL

namespace RAT

lemma leFlip {x y:Rat} (h:x≤y): (-y≤-x) := by simp;exact h

lemma ltFlip {x y:Rat} (h:x<y): ((-y)<(-x)) := by simp;exact h

lemma leAddLt {w x y z:Rat} (h1:x≤y) (h2:w<z) : ((x+w)<(y+z)) := calc
  x+w ≤ y+w := by simp [h1]
  _ < y+z := by simp [h2]

lemma leAddLe {w x y z:Rat} (h1:x≤y) (h2:w≤z) : ((x+w)≤(y+z)) := calc
  x+w ≤ y+w := by simp [h1]
   _ ≤  y+z := by simp [h2]

lemma addLeAddMpr {x y:Rat} (h:x≤y) (z:Real) : x+z ≤ y+z := by simp [h]

lemma addLtAddMpr {x y:Rat} (h:x<y) (z:Real) : x+z < y+z := by simp [h]

lemma mulNonNegLeMulNonMegMpr {x y z:Rat} (h1:x≤y) (h2:0≤z) : x*z ≤ y*z := by 
  by_cases hc: 0≤x 
  · have p2: 0≤z := h2
    have p1 := calc 
      0 ≤ x := hc
      _ ≤ y := h1
    have p3:z≤z := by simp
    exact mul_le_mul h1 p3 p2 p1
  · push_neg at hc
    replace hc: 0< (-x) := by simp [hc]
    let p1:= leFlip h1
    let p2:z≤z := by simp
    let p3:=mul_le_mul p1 p2 h2 hc.le
    have p4 :  -(y*z) ≤  -(x*z )  := calc 
      _ = -y * z := by simp
      _ ≤ -x * z :=p3
      _ = _  := by simp
    replace p4:=leFlip p4
    simp at p4;exact p4

lemma mulPosLtMulPosMpr {x y z:Rat} (h1:x<y) (h2:0<z) : x*z < y*z := by
  have p1:x*z ≠ y*z := by
    by_contra hc
    simp at hc
    cases' hc with H1 H2
    · exact absurd H1 h1.ne
    · exact absurd H2 (h2.ne).symm
  let p2:=mulNonNegLeMulNonMegMpr h1.le h2.le
  exact p2.lt_of_ne p1
      
lemma mulNegLeMulNegMpr {x y z:Rat} (h1:x≤y) (h2:z≤0) : y*z≤x*z  := by 
  have p1:0≤ (-z) := by simp [h2]
  let p2:= leFlip ( mulNonNegLeMulNonMegMpr  h1 p1)
  simp at p2;exact p2
    
lemma mulNegLtMulNegMpr {x y z:Rat} (h1:x<y) (h2:z<0) : y*z<x*z  := by 
  have p1:x*z ≠ y*z := by
    by_contra hc
    simp at hc
    cases' hc with H1 H2
    · exact absurd H1 h1.ne
    · exact absurd H2 (h2.ne)
  let p2:=mulNegLeMulNegMpr h1.le h2.le
  exact p2.lt_of_ne p1.symm

lemma invLeInvMpr {x y:Rat} (h1:0<x) (h2:x≤y): 1/y ≤ 1/x :=by
  have p1 := calc
    _ < _ := h1
    _ ≤ _ :=h2
  simp
  exact (inv_le_inv p1 h1).mpr h2

lemma invNegEqNegInv {x:Rat}: 1/(-x) = - (1/x) := by 
  simp
  exact inv_neg

lemma posInvIsPos {x:Rat} (h:0<x):0<1/x := by simp [h]
  
end RAT

namespace FinProd

@[simp]
def setFinProd {N:Nat} {η:Fin N->Type u_1} (l:(n:Fin N)-> Set (η n)): 
Set (∀n, η n) :={a:∀n, η n|∀n:Fin N, a n∈ l n }

end FinProd

namespace HEQ

lemma congr_fun_heq' {β1 β2:Sort u_1} {α:Sort u_2} {f:α->β1} {g:α->β2} (a:α) :
(β1=β2)->(HEq f g)->HEq (f a) (g a)  := by
  intro h1 h2
  cases h1; exact heq_iff_eq.mpr (congr_heq h2 (@HEq.rfl _ a))

lemma congr_heq' {β1 β2:Sort u_1} {α1 α2:Sort u_2} {x:α1}{y:α2} {f:α1->β1} {g:α2->β2} 
(h1:β1=β2) (h2 : HEq f g)  (h3 : HEq x y): HEq (f x) (g y) := by 
  cases h1; exact heq_iff_eq.mpr (congr_heq h2 h3)

end HEQ

namespace REAL

lemma realExistsFloor (x:ℝ):
∃ (fl : ℤ), ↑fl ≤ x ∧ ∀ (z : ℤ), ↑z ≤ x → z ≤ fl :=Real.exists_floor x

lemma realExistsCeiling (x:ℝ):
∃ (cl : ℤ), x ≤ ↑cl ∧ ∀ (z : ℤ), x ≤ ↑z → cl ≤ z :=by
  refine' Exists.elim  (realExistsFloor x) _
  intro fl hfl
  have p1:x< fl+1 := by
    by_contra hc; push_neg at hc
    replace hc :=hfl.right (fl+1) (by simp [hc])
    simp at hc
  by_cases c:∃k:ℤ , x = k
  · refine' Exists.elim c _ 
    intro k hk
    refine' ⟨k,by rw [hk],_ ⟩ 
    intro z hz; rw [hk] at hz
    simp at hz; exact hz
  · refine' ⟨fl+1,by simp; exact p1.le ,_⟩ 
    intro z hz
    by_contra hc; push_neg at hc
    let p2:=calc 
      ↑z ≤ (↑fl:Real) := by simp ;exact (Int.le_of_lt_add_one (hc)) 
      _ ≤ x := hfl.left
    replace p2:=le_antisymm p2 hz
    push_neg at c; 
    exact (c z) p2.symm

lemma realNonnegMulMaxEqMaxMulNonneg {a x y :ℝ}(h:0≤a): a*(x⊔y) = (a*x ⊔ a*y) := by
  by_cases c:x≤y
  · simp [c]
    calc
      _ = x*a := mul_comm _ _
      _ ≤ y*a := mulNonNegLeMulNonMegMpr c h
      _ = _ := mul_comm _ _
  · push_neg at c
    simp [c.le]
    calc
      _ = y*a := mul_comm _ _
      _ ≤ x*a :=mulNonNegLeMulNonMegMpr c.le h
      _ = _ := mul_comm _ _

lemma realNonnegMulMinEqMinMulNonneg {a x y:ℝ} (h:0≤a): a*(x⊓y) = (a*x ⊓ a*y) := by
  by_cases c:x≤y
  · simp [c]
    calc
      _ = x*a := mul_comm _ _
      _ ≤ y*a := mulNonNegLeMulNonMegMpr c h
      _ = _ := mul_comm _ _   
  · push_neg at c
    simp [c.le]
    calc
      _ = y*a := mul_comm _ _
      _ ≤ x*a :=mulNonNegLeMulNonMegMpr c.le h
      _ = _ := mul_comm _ _

end REAL

attribute [simp] List.flatten

