import Mathlib.Data.Fintype.Basic
import GradMath.Basic.Basic
import Mathlib.Algebra.BigOperators.Basic

open Multiset Finset
open Classical SET

universe u_1 u_2
variable {α:Type u_1} {γ: Type u_2}  (Ω:Finset α ) 

namespace CombinatorialNum

structure Combin (n:Nat) where
  nontriv:(1≤n)∧(n≤Ω.card):=by simp
  combin:Finset (Finset (↑ Ω.toSet)) 
  card_eq_n: ∀{s}, s∈combin -> s.card=n
  all_is_in: ∀{s:Finset (↑ Ω.toSet)}, (h: s.card=n)->s∈combin

structure Arrang (n:Nat) where
  nontriv:(1≤n)∧(n≤Ω.card):=by simp
  arrang:Finset (List (↑ Ω.toSet))
  nodup_len_n: ∀{l}, l∈arrang -> (l.Nodup)∧(l.length=n)
  all_is_in: ∀ {l: List (↑ Ω.toSet)}, (l.Nodup∧l.length=n)->l∈arrang

open FINSET LIST

theorem meaningOfMultip'  {s:Finset α} {f:α->Nat} (h:∀{a:α}, (a∈s)-> f a =k)
  :  s.sum f = k*s.card:= by 
  have h2  {t:Finset α}: t.card = t.val.toList.length  := by rw [ Finset.card_def];simp
  let rec aux {t:Finset α } (l:Nat) (p:t.card=l) (g:α ->Nat) (h':∀{a:α}, (a∈t)-> g a =k)
  : sum (Multiset.map g t.val) = k * (Finset.card t):=by
    match l with
    |0 => 
      have fact1:  t.card =0 ↔ t = ∅ :=by simp
      have lh1: t=∅ := fact1.mp p
      have lh2: t.val = 0 := by simp [lh1]
      rw [lh2,p];simp 
    |n+1 =>
      have lh1: t.card >0 :=by simp [p]
      have lp1: ∃x:α, x∈t := Finset.Nonempty.bex <|Finset.card_pos.mp lh1
      have lp2: ∀x:α, (x∈t) ->∃(x:α ), (x∈t.val)∧(x∈t) := by 
        intro y lhy;
        exact ⟨y,⟨by simp [lhy,Finset.mem_val,Exists.intro],lhy⟩⟩ 
      have lp3: ∃x:α, (x∈t.val)∧(x∈t):=Exists.elim lp1 lp2
      exact Exists.elim lp3 (by
        intro x lh3
        have lh4:∃m', t.val=x::ₘm' := Multiset.exists_cons_of_mem lh3.left
        exact Exists.elim lh4 (by
          intro m' lh5
          have lp4 : t.card=m'.toList.length+1:= by rw[h2,lh5];simp
          rw [lh5] ;simp;
          have lp5: g x =k := h' lh3.right
          rw [lp5,lp4,mul_add];
          have fact2: Nodup (x::ₘm')->(Nodup m'):=by simp 
          have lp6: Nodup (x::ₘm'):= by simp[<-lh5,t.nodup]
          have lp7:Nodup m':=fact2 lp6
          let t':={val:=m',nodup:=lp7:Finset α}
          have lp8: (x::ₘm').toList.length= n+1:=by rw [<-lh5,<-h2];assumption
          have lp9: (x::ₘm').toList.length=(m'.toList.length) +1:=by simp 
          have lp10:(m'.toList.length) =n :=
            calc
              (m').toList.length= (m').toList.length + 1 -1 :=by simp
              _ = (x::ₘm').toList.length -1 :=by rw [<-lp9]
              _ = n  := by rw [lp8];simp
          have lp11 :t'.card =n :=
            calc
              t'.card = m'.toList.length := by simp 
              _ = n :=by rw [lp10]
          have lp12: t'.val≤t.val:=by rw [lh5];simp [Multiset.le_cons_self]
          have lp13: t'⊆t := Finset.val_le_iff.mp lp12
          let h'' :∀{a:α}, (a∈t')-> g a =k:= by 
            intro a hp'
            have hp'':a∈t:= (Finset.subset_iff.mp lp13) hp'
            exact h' hp''
          let auxP := aux n lp11 g h''
          have lh6:List.length (Multiset.toList m')= Finset.card t':=by simp  [h2]
          have auxP': k*List.length (Multiset.toList m')= sum (Multiset.map g m') 
            :=by rw [auxP,<-lh6]
          rw [auxP'] ;rw [Nat.add_comm];simp
        ))
  let m:=s.card
  have q:s.card=m:= by rfl
  exact aux m q f h 

theorem meaningOfMultip  {l:List α} {f:α->Nat} (h: ∀{a:α}, (a∈l)-> f a =k)
: l.foldr (fun (b:α) (v:Nat)=> (f b)+v) 0 = k*l.length:= by  
  set L:=l with H
  induction' l with a l' hd
  case nil => simp_all
  case cons => 
    simp [Nat.mul_succ];
    have h':∀{a:α},a∈l' → f a=k := by
      intro a' p1
      replace p1:a'∈a::l' := by simp_all
      exact h p1
    rw [hd h']
    have p1: a∈L:= by simp_all
    replace h:= h p1
    rw [h];abel;simp

theorem leqAddUp' {s:Finset α} (f:α->Nat×Nat) (h:∀{a:α},a∈s->(f a).1≤(f a).2):
s.sum (fun x=>(f x).1) ≤ s.sum (fun x=>(f x).2):= by
  let rec aux {t:Finset α} (n:Nat) (H:n=t.card) (g:α->Nat×Nat)
  (i:∀{a:α},a∈t->(g a).1≤(g a).2)
    : t.sum (fun x=>(g x).1) ≤ t.sum (fun x=>(g x).2):=by
    match n with
    |0 =>
      have p1:t=∅:=  finsetEmptyIff.mpr H.symm
      rw [p1];simp
    |n'+1 =>
      let goal:= t.sum (fun x=>(g x).1) ≤  t.sum (fun x=>(g x).2)
      have p1: 0 < t.card := calc
        0 < n'.succ := by simp
        _ = t.card := H
      have p2: ∃x:α, x∈t := Nonempty.bex <|card_pos.mp p1
      have p3: ∀x:α, x∈t -> goal:=by 
        intro x p4
        let p5:= exists_cons_of_mem p4
        have p6: ∀ u, t.val = x::ₘu -> goal:= by
          intro u p7
          let p8:=t.nodup;rw [p7] at p8;simp at p8
          replace p8:u.Nodup:= by simp [p8]
          let U:Finset α:=⟨u,p8⟩ 
          have i':∀{a:α},a∈U->(g a).1≤(g a).2 := by
            intro a p9
            have p10: a∈t.val :=by simp_all
            replace p10: a∈t := mem_val.mp p10
            exact i p10
          have p9':n'=U.card:= by
            have p10:t.val.toList.length= u.toList.length+1:=by
              simp [p7]
            have p11:t.card=t.val.toList.length :=calc
              t.card = t.toList.length := by simp
              _ = t.val.toList.length := by simp [Finset.toList]
            have p12:U.card = u.toList.length := by simp
            rw [←p11,←p12] at p10;let p13:= (H.symm ▸ p10)
            simp at p13;simp [p13]
          let p9:=aux n' (p9') g i'
          let p10 :=Nat.add_le_add (p9) (i p4)
          have p11:(Finset.sum t fun x => (g x).fst) = 
          (g x).fst + sum (Multiset.map (fun x => (g x).fst) u) := by
            simp [Finset.sum,p7]
          calc
          _ = _ := p11
          (g x).fst + sum (Multiset.map (fun x => (g x).fst) u)  
            = sum (Multiset.map (fun x => (g x).fst) u) + (g x).fst 
              := by simp [add_comm]
          _ ≤ _ := p10
          _ =Finset.sum t fun x => (g x).snd := by simp [Finset.sum,p7,add_comm]
        exact Exists.elim p5 p6
      exact Exists.elim p2 p3
  exact aux s.card (by simp) f h

theorem leqAddUp {l:List α} (f:α->Nat×Nat) (h:∀{a:α},a∈l->(f a).1≤(f a).2):
l.foldr (fun a n=> ((f a).1 + n)) 0 ≤l.foldr (fun a n=> ((f a).2 + n)) 0 := by
  set L:=l with H
  induction' l with a l' hd
  case nil=>simp
  case cons => 
    simp
    have p1:a∈L:= by simp 
    replace p1:=h p1
    have p2:∀ {a:α},a∈l' →(f a).1≤(f a).2:= by
      intro x p
      have p3: x∈L:=by simp [p]
      exact h p3
    calc
      (f a).1 + l'.foldr (fun a n => (f a).fst + n) 0 
        ≤ (f a).2 + l'.foldr (fun a n => (f a).fst + n) 0
            := by simp [p1]
      _ ≤_  := by simp [hd p2]

variable [inst1:DecidableEq α ] 

noncomputable def Arrang.arrang1 (h:Ω≠∅ ) : Arrang Ω 1 := 
  let f :(Subtype Ω.toSet)->List (↑ Ω.toSet):= fun x => [x ]
  {
  nontriv:=⟨by simp_all, Nat.succ_le_iff.mp 
    (finsetNonEmptyIff.mp (finsetNeqEmptyIff.mp h))⟩ 
  arrang:=by 
    let l:=Ω.toSubtype.toList.map f
    have p2:l.Nodup := by
      apply listNodupIff.mpr
      intro i j h1 h2 h3
      replace h1:i <Ω.toSubtype.toList.length:= by simp_all
      replace h2:j<Ω.toSubtype.toList.length:= by simp_all
      let p3: (Ω.toSubtype.toList)[i] ≠ (Ω.toSubtype.toList)[j]
        :=(listNodupIff.mp (finsetToListNodup (Ω.toSubtype))) h1 h2 h3
      have p4:l[i]=f (Ω.toSubtype.toList[i]):= by simp_all
      have p5:l[j]=f (Ω.toSubtype.toList[j]):= by simp_all
      have p6:0<l[i].length:= by simp_all
      have p7:0<l[j].length:= by simp_all
      apply (listNeqMpr p6 p7 )
      simp_rw [p4,p5];simp;exact p3
    exact ⟨l,p2⟩ 
  nodup_len_n:=by 
    intro l h
    have p1:l.length=1:= by 
      let p2:= LIST.listMemIff.mp h
      exact Exists.elim p2 (by
        intro n p2
        exact Exists.elim p2 (by
          intro h p3
          have p4:n<Ω.toSubtype.toList.length:= by simp_all
          replace p3:l=f (Ω.toSubtype.toList[n]):= by simp_all
          simp [p3]
        ))
    exact ⟨ listNodupLenEqOne p1,p1⟩ 
  all_is_in:=by
    intro t h
    have p1:0<t.length:= by simp_all
    have p2:⟨ t[0].val,t[0].property⟩  ∈  Ω.toSubtype.toList:=by
      let p4:=toSubtypeMemMpr Ω  t[0].property
      have p5:t[0]=⟨t[0].val,t[0].property ⟩ := by rfl
      simp_rw [p5.symm] at p4
      exact finsetMemToListIff.mpr p4
    have p3:t=[t[0]]:=by
      apply listEqIff.mpr
      have p4:t.length=[t[0]].length := by simp_all
      have p5:∀{n:ℕ}(h1:n<t.length){h2:n<[t[0]].length},t[n]=[t[0]][n]:= by
        intro n h1 h2 
        have p6:n=0:= by simp_all
        simp_rw [p6];simp
      exact ⟨p4,p5 ⟩ 
    have p4:[t[0]]∈ Ω.toSubtype.toList.map f
      := listMemMapMpr f p2
    rw [p3];exact p4
  }

set_option maxHeartbeats 300000
noncomputable  def Arrang.succ {kk:Nat} (h:kk<Ω.card) (a:Arrang Ω kk) : Arrang Ω (kk+1):= by
  have nontriv: (1≤(kk+1))∧((kk+1)≤Ω.card):= by 
    apply And.intro
    · simp_all
    · simp [Nat.succ_le_iff.mpr h]
  set L:=a.arrang.toList.map 
    (fun (l:List (Subtype Ω.toSet)) 
      => ((Ω.toSubtype.val - ↑l).toList.map (fun (x:Subtype Ω.toSet)=>l++[x]))) with HH
  set alist:=L.flatten
  have  nodup_len_n': ∀{t}, t∈alist -> t.Nodup∧t.length=kk+1 := by 
    intro t h1
    let p1:=(@listMemIff _ t alist).mp h1
    exact Exists.elim p1 ( by
      intro n h1
      exact Exists.elim h1 ( by
        intro h1 h2
        let idx:=L.indexRecover h1
        let p2:=indexRecoverIsValid h1
        let p2_1:=p2.1;let p2_2:=p2.2
        let p3:=indexRecoverEqOrig h1
        set l:=L[idx.1] with h3
        have p4:l[idx.2]=t := calc
          l[idx.2] = L[idx.1][idx.2] := rfl
          _ = L.flatten[n] := by rw [p3]
          _ = alist[n] := by rfl
          _ = t := h2
        let p5: l∈L :=listMemIff.mpr ⟨idx.1,p2_1,h3⟩ 
        rw [HH] at p5; 
        replace p5:=listMemIff.mp p5          
        exact Exists.elim p5 ( by
          intro m p6
          exact Exists.elim p6 ( by
            intro p6 p7
            have p8: (Finset.toList a.arrang).length = 
              ((Finset.toList a.arrang).map 
              (fun l => List.map (fun x => l ++ [x]) ((Ω.toSubtype.val - ↑l).toList ))).length
                := by simp
            replace p6:= p8.symm ▸ p6
            have p9: ((Finset.toList a.arrang).map 
              (fun l => List.map (fun x => l ++ [x]) ((Ω.toSubtype.val - ↑l).toList )))[m]
              = (fun l => List.map (fun x => l ++ [x]) ((Ω.toSubtype.val - ↑l).toList ))
              (Finset.toList a.arrang)[m] := by simp
            replace p7 := p9 ▸ p7 ;
            set t':List (Subtype Ω.toSet):=(Finset.toList a.arrang)[m] 
            replace p7:=calc
              ((Ω.toSubtype.val - ↑t').toList ).map (fun x => t'++[x])
              = (fun l => List.map (fun x => l ++ [x]) ((Ω.toSubtype.val - ↑l).toList ))
                (Finset.toList a.arrang)[m]  := rfl 
              _ = l :=p7
            let p5: t∈l :=listMemIff.mpr ⟨idx.2,p2_2,p4 ⟩ 
            replace p5:= p7.symm ▸ p5
            replace p5:=listMemMapIff.mp p5
            exact Exists.elim p5 ( by
              intro e p5
              have p10:= listGetIsMem p6
              replace p10: t'∈a.arrang.toList := p10
              replace p10 :=a.nodup_len_n (Finset.mem_toList.mp p10)
              replace p4:=Multiset.mem_toList.mp p5.left
              replace p5:=p5.2
              replace p4:=(Multiset.mem_sub_of_nodup Ω.toSubtype.nodup).mp p4
              have p11: t.Nodup := by 
                apply listNodupIff.mpr
                intro i j hh1 hh2 hh3
                rw [p5.symm] at hh1 hh2;
                by_cases c1:i<t'.length 
                · let p12:=listGetIsMem c1
                  have p13:t' = t.take t'.length :=by
                    rw [p5.symm];simp
                  have p14: t'.length ≤ t.length := by rw [p5.symm];simp
                  let p15:=listTakeIsSublist p14 c1
                  simp_rw [p13.symm] at p15;
                  by_cases c2:j<t'.length
                  · let p16:=listTakeIsSublist p14 c2
                    simp_rw [p13.symm] at p16;
                    have p18: t'[i]≠t'[j]
                      :=(@listNodupIff _ t').mp p10.left c1 c2 hh3
                    rw [p15,p16] at p18;exact p18
                  · push_neg at c2
                    have p16: 0<List.length (t' ++ [e]) := by simp
                    let p17:=(Nat.lt_iff_le_pred p16).mp hh2
                    simp at p17;replace p17:= le_antisymm c2 p17
                    have p18: t=t'++[e]++[] := by rw [p5] ;simp
                    replace p18:=listSplitByElemRev p18
                    simp_rw [p17] at p18
                    by_contra hc               
                    let p19:=p4.right;simp at p19 
                    replace p15:=p15 ▸ p12 
                    rw [hc,p18] at p15
                    exact p19 p15
                · push_neg at c1
                  have p12: 0<List.length (t' ++ [e]) := by simp
                  let p13:=(Nat.lt_iff_le_pred p12).mp hh1
                  simp at p13;replace p13:= le_antisymm c1 p13
                  by_cases c2:j<t'.length
                  · have p14: t'.length ≤ t.length := by rw [p5.symm];simp
                    let p15:=listTakeIsSublist p14 c2
                    have p16:t=t'++[e]++[] := by rw [p5] ;simp
                    replace p16:=listSplitByElemRev p16
                    simp_rw [p13] at p16
                    by_contra hc
                    let p17:=listGetIsMem c2
                    have p18:t' = t.take t'.length :=by
                      rw [p5.symm];simp
                    have p19: j<(t.take t'.length).length :=by rw [p18.symm];exact c2
                    have p20: (t.take t'.length)[j] = t'[j]:= by simp_rw [p18.symm]
                    replace p20:=p15 ▸ p20;
                    replace p20:=p20.symm ▸ p17
                    rw [hc.symm,p16] at p20
                    replace p4:=p4.right;simp at p4;
                    exact p4 p20
                  · push_neg at c2
                    have p16: 0<List.length (t' ++ [e]) := by simp
                    let p17:=(Nat.lt_iff_le_pred p16).mp hh2
                    simp at p17;replace p17:= le_antisymm c2 p17
                    by_contra
                    exact  (hh3 (p13 ▸ p17))
              have p12:t.length=kk+1 := by
                rw [p5.symm];simp;exact p10.right
              exact ⟨p11,p12⟩ 
    )))))
  have nodupAlist:alist.Nodup := by 
    apply listNodupIff.mpr
    intro i j h1 h2 h3 
    have p1: L.indexRecover h1 ≠ L.indexRecover h2 :=by 
      by_contra hc
      exact h3 (indexRecoverInj h1 h2 hc)
    by_cases c1:(L.indexRecover h1).1 = (L.indexRecover h2).1
    · have p2:(L.indexRecover h1).2 ≠  (L.indexRecover h2).2 := by
        by_contra hc
        exact p1 (
          Prod.eq_iff_fst_eq_snd_eq.mpr ⟨c1,hc ⟩ )  
      let p3:=indexRecoverIsValid h1
      let p3_1:=p3.1;let p3_2:=p3.2
      let p4:=indexRecoverEqOrig h1
      set l:=L[(L.indexRecover h1).1] with  h4
      have p5:l[(L.indexRecover h1).2]=alist[i] := calc
        l[(L.indexRecover h1).2] = L[(L.indexRecover h1).1][(L.indexRecover h1).2] 
              := rfl
        _ = L.flatten[i] := by rw [p4]
        _ = alist[i] := by rfl
      replace p3:=indexRecoverIsValid h2
      let p3_1':=p3.1;let p3_2':=p3.2
      replace p4:=indexRecoverEqOrig h2
      have p6:l=L[(L.indexRecover h2).1] := by 
        simp_rw [c1.symm]
      have p7:(L.indexRecover h2).2 <l.length := by rw[p6];exact p3_2'
      have p8:l[(L.indexRecover h2).2]=alist[j] := calc
        l[(L.indexRecover h2).2] = L[(L.indexRecover h2).1][(L.indexRecover h2).2]
              :=by simp_rw [p6]
        _ = L.flatten[j] := by rw [p4]
        _ = alist[j] := by rfl
      let p9: l∈L :=listMemIff.mpr ⟨(L.indexRecover h1).1,p3_1,h4⟩ 
      rw [HH] at p9
      replace p9:=listMemMapIff.mp p9
      exact Exists.elim p9 ( by
        intro t' h5
        have p10: Ω.toSubtype.val= ↑Ω.toSubtype.val.toList := by simp
        have p11:Ω.toSubtype.val-↑t'= ↑(Ω.toSubtype.val.toList.diff t') :=  calc
          Ω.toSubtype.val-↑t' = ↑Ω.toSubtype.val.toList - ↑t' := by rw [p10] ;simp
          _ = ↑(Ω.toSubtype.val.toList.diff t') := Multiset.coe_sub _ _
        replace p10:=  p10 ▸ (Ω.toSubtype.nodup)
        replace p10:=p11.symm ▸ Multiset.coe_nodup.mpr (List.Nodup.diff p10)
        replace p11:Ω.toSubtype.val-↑t' = ↑ (Ω.toSubtype.val-↑t').toList := by simp
        replace p10:=Multiset.coe_nodup.mp (p11 ▸ p10)
        replace h5:=h5.right
        have p12':(List.indexRecover L h1).2<((Ω.toSubtype.val-↑t').toList.map (t'++[.])).length 
          := by rw [h5];exact p3_2
        rw [p6.symm] at p3_2'
        have p13':(List.indexRecover L h2).2<((Ω.toSubtype.val-↑t').toList.map (t'++[.])).length 
          := by rw [h5];exact p3_2'
        have p12'':(List.indexRecover L h1).2<(Ω.toSubtype.val-↑t').toList.length := calc
          _ < ((Ω.toSubtype.val-↑t').toList.map (t'++[.])).length := p12'
          _ = (Ω.toSubtype.val-↑t').toList.length := by simp
        have p13'':(List.indexRecover L h2).2<(Ω.toSubtype.val-↑t').toList.length := calc
          _ < ((Ω.toSubtype.val-↑t').toList.map (t'++[.])).length := p13'
          _ = (Ω.toSubtype.val-↑t').toList.length := by simp
        have p12:
          l[(List.indexRecover L h1).2] =
          t'++ [(Ω.toSubtype.val-↑t').toList[(List.indexRecover L h1).2]]++[] :=calc 
          l[(List.indexRecover L h1).2] = 
          ((Ω.toSubtype.val-↑t').toList.map (t'++[.]))[(List.indexRecover L h1).2] 
                := by simp_rw [h5]
          _ = (t'++[.]) (Ω.toSubtype.val-↑t').toList[(List.indexRecover L h1).2] 
                := by simp
          _ = t'++ [(Ω.toSubtype.val-↑t').toList[(List.indexRecover L h1).2]]++[]
                := by simp
        have p13:
          l[(List.indexRecover L h2).2] =
          t'++ [(Ω.toSubtype.val-↑t').toList[(List.indexRecover L h2).2]]++[] :=calc 
          l[(List.indexRecover L h2).2] = 
          ((Ω.toSubtype.val-↑t').toList.map (t'++[.]))[(List.indexRecover L h2).2] 
                := by simp_rw [h5]
          _ = (t'++[.]) (Ω.toSubtype.val-↑t').toList[(List.indexRecover L h2).2] 
                := by simp
          _ = t'++ [(Ω.toSubtype.val-↑t').toList[(List.indexRecover L h2).2]]++[]
                := by simp
        replace p12:=listSplitByElemRev p12
        replace p13:=listSplitByElemRev p13
        replace p10:∀ {i j : ℕ}
          (h1 : i <((Ω.toSubtype).val - ↑t').toList.length)
          (h2 : j <((Ω.toSubtype).val - ↑t').toList.length),
          i ≠ j → (((Ω.toSubtype).val - ↑t').toList)[i] 
          ≠ (((Ω.toSubtype).val - ↑t').toList)[j]:=(listNodupIff.mp p10 )
        rw [p5.symm,p8.symm] 
        replace p10:=p10 p12'' p13''  p2
        rw [p12.symm,p13.symm] at p10;
        apply listNeqMpr
        exact p10
      )
    · let p3:=indexRecoverIsValid h1
      let p3_1:=p3.1;let p3_2:=p3.2
      let p4:=indexRecoverEqOrig h1
      set l:=L[(L.indexRecover h1).1] with  h4
      have p5:l[(L.indexRecover h1).2]=alist[i] := calc
        l[(L.indexRecover h1).2] = L[(L.indexRecover h1).1][(L.indexRecover h1).2] 
              := rfl
        _ = L.flatten[i] := by rw [p4]
        _ = alist[i] := by rfl
      let p3':=indexRecoverIsValid h2
      let p3_1':=p3'.1;let p3_2':=p3'.2
      let p4':=indexRecoverEqOrig h2
      set l':=L[(L.indexRecover h2).1] with  h4'
      have p5':l'[(L.indexRecover h2).2]=alist[j] := calc
        l'[(L.indexRecover h2).2] = L[(L.indexRecover h2).1][(L.indexRecover h2).2] 
              := rfl
        _ = L.flatten[j] := by rw [p4']
        _ = alist[j] := by rfl
      have p60: a.arrang.toList.length = L.length := by simp
      have p6_1':=p60.symm ▸ p3_1'
      have p6_1:= p60.symm ▸ p3_1
      set t0:List (Subtype Ω.toSet):=a.arrang.toList[(L.indexRecover h1).1] with h6
      set t0':List (Subtype Ω.toSet):=a.arrang.toList[(L.indexRecover h2).1] with h6'
      have p6: l = (fun (l:List (Subtype Ω.toSet))=>
        ((Ω.toSubtype.val - ↑l).toList.map (fun (x:Subtype Ω.toSet)=>l++[x])))
          a.arrang.toList[(L.indexRecover h1).1]  := listMapNEqFN a.arrang.toList 
            (fun (l:List (Subtype Ω.toSet)) => ((Ω.toSubtype.val - ↑l).toList.map 
            (fun (x:Subtype Ω.toSet)=>l++[x])))  p6_1
      have p6':l' = (fun (l:List (Subtype Ω.toSet))=>
        ((Ω.toSubtype.val - ↑l).toList.map (fun (x:Subtype Ω.toSet)=>l++[x]))) 
        a.arrang.toList[(L.indexRecover h2).1] 
          := listMapNEqFN a.arrang.toList (fun (l:List (Subtype Ω.toSet)) 
            => ((Ω.toSubtype.val - ↑l).toList.map (fun (x:Subtype Ω.toSet)=>l++[x])))  p6_1'
      replace p6:=calc
        l = _ :=p6
        _ = (Ω.toSubtype.val - ↑t0).toList.map (fun x=>t0++[x]) := by rfl
      replace p6':=calc
        l' = _ :=p6'
        _ = (Ω.toSubtype.val - ↑t0').toList.map (fun x=>t0'++[x]) := by rfl
      have p6_2:(L.indexRecover h1).2<
        ( (Ω.toSubtype.val - ↑t0).toList.map (fun x=>t0++[x])).length :=by 
        rw [p6.symm];exact p3_2
      have p6_2':(L.indexRecover h2).2<
        ( (Ω.toSubtype.val - ↑t0').toList.map (fun x=>t0'++[x])).length :=by 
        rw [p6'.symm];exact p3_2'
      have p6_3 :( (Ω.toSubtype.val - ↑t0).toList.map (fun x=>t0++[x])).length
        = (Ω.toSubtype.val - ↑t0).toList.length := by simp
      replace p6_3 := p6_3 ▸ p6_2
      have p6_3' :( (Ω.toSubtype.val - ↑t0').toList.map (fun x=>t0'++[x])).length
        = (Ω.toSubtype.val - ↑t0').toList.length := by simp
      replace p6_3' := p6_3' ▸ p6_2'
      replace p6:=calc
        alist[i] = _ := p5.symm
        _ = ( (Ω.toSubtype.val - ↑t0).toList.map (fun x=>t0++[x]))[(L.indexRecover h1).2]
              := by simp_rw [p6]
        _ =  t0++[ (Ω.toSubtype.val - ↑t0).toList[(L.indexRecover h1).2]]
              := by simp
      replace p6':=calc
        alist[j] = _ := p5'.symm
        _ = ( (Ω.toSubtype.val - ↑t0').toList.map (fun x=>t0'++[x]))[(L.indexRecover h2).2]
              := by simp_rw [p6']
        _ =  t0'++[ (Ω.toSubtype.val - ↑t0').toList[(L.indexRecover h2).2]]
              := by simp
      have p7:∀ {i j : ℕ} (h1 : i < List.length (Finset.toList a.arrang)) 
        (h2 : j < List.length (Finset.toList a.arrang)),    i ≠ j → 
        (Finset.toList a.arrang)[i] ≠ (Finset.toList a.arrang)[j]:= listNodupIff.mp
          (FINSET.finsetToListNodup a.arrang)
      have p8:a.arrang.toList.length = L.length := by simp 
      rw [p8.symm] at p3_1 p3_1'
      let p7':= p7 p3_1 p3_1' c1
      rw [←h6,←h6'] at p7'
      by_contra hc
      let p8:=listGetIsMem p6_1;rw [← h6] at p8;
      replace p8:t0∈ a.arrang :=Finset.mem_toList.mp p8
      let p8':=listGetIsMem p6_1';rw [← h6'] at p8';
      replace p8':t0'∈ a.arrang :=Finset.mem_toList.mp p8'
      have p9:t0.length=kk:=(a.nodup_len_n p8).right;
      have p9':t0'.length=kk:=(a.nodup_len_n p8').right
      have p10:t0.length=t0'.length := by rw [p9,p9']
      have p11:alist[i].take (t0.length) = t0 := by 
        rw [p6];simp
      have p11':alist[j].take (t0'.length) = t0' := by
        rw [p6'];simp
      replace p11:=p10 ▸ p11
      replace p11:= hc ▸ p11   
      replace p11:= p11' ▸ p11
      exact p7' p11.symm
  have all_is_in' : ∀l: List (Subtype Ω.toSet), (l.Nodup∧l.length=kk+1)->l∈alist
  := by 
    intro (l:List _) h
    have p1:(l.take kk).length=kk := listTakeLenLeq (by simp_all)
    have p6:kk<l.length := by simp_all
    have p2:(l.take kk).Nodup := by
      apply listNodupIff.mpr
      intro i j h1 h2 h3
      have p3:kk≤l.length := by
        rw [p1.symm];simp
      have p4:= p1 ▸ h1 ;have p5:= p1 ▸ h2
      let p6:=listTakeIsSublist p3 p4
      let p7:=listTakeIsSublist p3 p5
      rw [p6,p7]
      have p8:=calc
        i < (l.take kk).length := h1
        _ ≤ l.length := by simp
      have p9:= calc
        j < (l.take kk).length := h2
        _ ≤ l.length := by simp
      exact (listNodupIff.mp h.left) p8 p9 h3
    have p3:=a.all_is_in  ⟨p2,p1⟩ 
    let f:=(fun l => List.map (fun x => l ++ [x]) 
      (Multiset.toList ((toSubtype Ω).val - ((↑l):Multiset _)))) 
    have p4:f (l.take kk)∈L:= List.mem_map_of_mem f (Finset.mem_toList.mpr p3)
    have p5: f (l.take kk) = ((toSubtype Ω).val - 
      ((↑(l.take kk)):Multiset _)).toList.map (fun x => (l.take kk)++[x]):= by rfl
    set x:=l[kk] with ←HH2
    let p7:=listSplitByElem p6 HH2
    let p8:=listDropLenLeq p6
    replace p8:=h.right ▸ p8;
    replace p8:=calc
      (l.drop (kk+1)).length = kk+1-(kk.succ) :=p8
      _ = 0 := by simp
    replace p8:=List.length_eq_zero.mp p8
    replace p7 := p8 ▸ p7;simp at p7
    let p9:=toSubtypeMemMpr' Ω  x
    have p10: Ω.toSubtype.val= ↑Ω.toSubtype.val.toList := by simp
    set l':=l.take kk 
    have p11:Ω.toSubtype.val-↑l'= ↑(Ω.toSubtype.val.toList.diff l') :=  calc
      Ω.toSubtype.val-↑l' = ↑Ω.toSubtype.val.toList - ↑l' := by rw [p10] ;simp
      _ = ↑(Ω.toSubtype.val.toList.diff l') := Multiset.coe_sub _ _
    have p12:x∉l':= by
      apply listNotMemIff.mpr
      intro m hm
      let hm':=calc
        m < l'.length := hm
        _ ≤ l.length := by simp
      let p13:=listNodupIff.mp h.left p6 hm'
      let p14:=(NAT.natLtIff.mp hm).left
      simp_rw [p1] at p14
      replace p14:= p13 p14.symm
      replace hm:= p1 ▸ hm
      replace p8:kk≤l.length := by
        rw [p1.symm];simp
      replace p13:=listTakeIsSublist p8 hm
      rw [p13.symm] at p14;exact p14
    replace p9:x∈Ω.toSubtype.val.toList :=by
      simp;exact p9
    replace p9:=List.mem_map_of_mem (fun y=>l'++[y]) 
      (List.mem_diff_of_mem p9 p12)
    replace p7:=calc
      l = l'++[x] :=p7
      _ = (fun y => l'++[y]) x := rfl
    rw [p7.symm] at p9
    have p13:= calc
      ↑((List.diff Ω.toSubtype.val.toList l').map (fun y=>l'++[y]))= 
      Multiset.map (fun y=>l'++[y]) (↑(List.diff Ω.toSubtype.val.toList l')) 
        := by simp
      _ = Multiset.map (fun y=>l'++[y]) ((toSubtype Ω).val - ↑l')
        := by rw [p11.symm]
    replace p9:=Multiset.mem_coe.mpr p9
    rw [p13] at p9
    replace p13:
      ↑(((toSubtype Ω).val - ↑l').toList) = (toSubtype Ω).val - ↑l'
        := by simp
    have p14:=calc
      Multiset.map (fun y => l' ++ [y]) ((toSubtype Ω).val - ↑l')
        = Multiset.map (fun y => l' ++ [y]) (↑(((toSubtype Ω).val - ↑l').toList)) 
          := congrArg _ p13.symm
      _ = ↑ ((((toSubtype Ω).val - ↑l').toList).map (fun y => l' ++ [y]))
        := Multiset.coe_map _ _
    replace p9:=p5.symm ▸ Multiset.mem_coe.mp (p14 ▸ p9)
    exact flatMemMpr L p9 p4
  let arrang:Finset (List (Subtype Ω.toSet)):=⟨alist,nodupAlist ⟩ 
  have nodup_len_n:∀{t},t ∈ arrang → List.Nodup t ∧ List.length t = kk + 1
    := by 
    intro t h
    have p1: t∈alist := Finset.mem_val.mpr h
    exact nodup_len_n' p1
  have all_is_in:∀{l:List (Subtype Ω.toSet)}, l.Nodup ∧ l.length = kk + 1 → l ∈ arrang
    := by 
    intro t h
    let p1:=all_is_in' t h
    exact Finset.mem_val.mp p1
  exact ⟨nontriv,arrang,nodup_len_n,all_is_in ⟩ 

set_option maxHeartbeats 200000

end CombinatorialNum

namespace Finset

noncomputable def arrang (Ω:Finset α) {kk:Nat} (h:(1≤kk)∧(kk≤Ω.card)):CombinatorialNum.Arrang Ω kk:= 
  match kk with 
  |0 => by
    let p1:=h.left
    simp at p1
  |.succ 0 =>  
    have p1:Ω≠∅:= by 
      by_contra hc
      let p2:=h.right
      simp [hc] at p2
    CombinatorialNum.Arrang.arrang1 Ω p1 
  |.succ (.succ n) => by 
    have p1:= calc
      n.succ ≤ n.succ.succ := Nat.le_succ _
      _ ≤ Ω.card := h.right
    have p2':0≤n := by simp
    have p2:=calc 
      1 =Nat.succ 0 := by simp
      _ ≤ n.succ :=Nat.succ_le_succ p2' 
    have p3:=calc 
      n.succ < n.succ.succ := by simp
      _ ≤  Ω.card := h.right
    exact CombinatorialNum.Arrang.succ Ω p3 (arrang Ω ⟨p2,p1⟩ )

end Finset

namespace  CombinatorialNum

open FINSET
variable [inst1:DecidableEq α ]

lemma arrangCardEqA.aux {kk:ℕ} {Ω:Finset α} (h:kk<Finset.card Ω)(a:Arrang Ω kk) : 
(Arrang.succ Ω h a).arrang.card = a.arrang.card * (Ω.card -kk) := by 
  simp [Arrang.succ]
  let g:=  ( (fun l:List (Subtype Ω.toSet) => List.map (fun x => l ++ [x]) 
    (Multiset.toList ((toSubtype Ω).val - ((↑l):Multiset _)))))
  let p1 :=LIST.flatLenEqSum  (a.arrang.toList.map g)
  have p2 {β:Type u_1} (L:List (List (β ))) :
    (List.flatten.f [] L).length=L.flatten.length  := rfl
  rw [← p2] at p1; rw [p1,List.map_map]
  have p3:∀{l:List _},(l∈a.arrang.toList)->
    ( ((fun a => List.length a) ∘ g) l ) = (Ω.card -kk) := by
    intro l h
    simp; rw [←Multiset.length_toList]
    let p4 :=a.nodup_len_n (Finset.mem_toList.mp h)
    set s:Finset (Subtype Ω.toSet) := ⟨(l:Multiset (Ω.toSet)),p4.left⟩ 
    have p5: s⊆Ω.toSubtype := by
      apply Finset.subset_iff.mpr
      intro x _
      exact toSubtypeMemMpr' Ω  x
    replace p5:=Finset.card_sdiff p5
    have p6:List.length (Multiset.toList (toSubtype Ω \ s).val) 
      = List.length (Multiset.toList ((toSubtype Ω).val - s.val)) 
        :=congrArg (fun x:Multiset _ => x.toList.length) 
          (Finset.sdiff_val Ω.toSubtype s)
    have p7: Finset.card (toSubtype Ω \ s)= (toSubtype Ω \ s).val.toList.length 
      := by rw [Multiset.length_toList];rw [Finset.card_def]
    replace p5:= p7 ▸ p5
    replace p5:= p6 ▸ p5
    replace p7: s.val = ((↑l):Multiset Ω.toSet) := rfl
    replace p5 := p7 ▸ p5;rw [p5]
    rw [toSubtypeCardEqOrig Ω ];simp;
    rw [p4.right];
  let p4:=meaningOfMultip p3;
  have hcomm : Commutative (fun (a b:Nat)=>a+b) := by 
    intro a b; simp [add_comm]
  have hassoc : Associative (fun (a b:Nat)=>a+b) := by 
    intro a b c ; simp [add_assoc]
  let p5:=List.foldl_eq_foldr hcomm hassoc 0 
    (a.arrang.toList.map ((fun a => List.length a)∘g))
  rw [p5]    
  let p6:=List.foldr_map  ((fun a => List.length a)∘g) (.+.) 
    a.arrang.toList 0 
  replace p6:=calc
    (Finset.card Ω - kk) * List.length (Finset.toList a.arrang)
     = List.foldr (fun b v => ((fun a => List.length a) ∘ g) b + v) 
      0 (Finset.toList a.arrang) := p4.symm
    _ = _ := p6.symm
  rw [p6.symm];simp [mul_comm]

open Nat

notation: 100 "A(" m "," n ")" => (m !)/((m-n) !)
notation: 100 "C(" m "," n ")" => A(m,n)/A(n,n)

theorem arrangUnique {Ω:Finset α} {a1 a2:Arrang Ω n} : a1=a2 := by
  have p1:a1.arrang=a2.arrang := by
    apply Finset.ext_iff.mpr
    intro t
    have mp:t∈a1.arrang -> t∈a2.arrang := by
      intro h
      exact a2.all_is_in (a1.nodup_len_n h)
    have mpr:t∈a2.arrang -> t∈a1.arrang := by
      intro h
      exact a1.all_is_in (a2.nodup_len_n h)
    exact ⟨mp,mpr⟩ 
  calc 
    a1 = ⟨_,a1.arrang,_,_ ⟩ := rfl 
    _ = ⟨_,a2.arrang,_,_ ⟩:= by simp_rw [p1]

theorem arrangCardEqA {n:Nat} (Ω:Finset α) (h:(1≤n)∧(n≤Ω.card)):
(Ω.arrang h).arrang.card = A(Ω.card,n) := by
  match n with
  |0 => 
    replace h:=h.left;simp at h
  |1 =>
    have p1:(Ω.arrang h).arrang.card=Ω.card := by
      simp [arrang,Arrang.arrang1];
    have p2:= calc
      0 < 1 := by simp
      _ ≤ Ω.card :=h.right
    replace p2:=Nat.mul_factorial_pred p2
    have p3: 0 < (Ω.card -1)! := by 
      apply NAT.natLtIff.mpr
      have p4: 0 ≤ (Ω.card -1)! := by simp
      let p5:=factorial_ne_zero (Ω.card -1)
      exact ⟨p5.symm,p4⟩ 
    replace p3:=Nat.mul_div_mul_right Ω.card 1 p3
    simp at p3;rw [p2] at p3
    rw [p3];exact p1
  |.succ (.succ n) => 
    have p1:= calc
      1 ≤ 1 +n := by simp
      _ = n.succ := by rw [add_comm]
    have p2:=calc
      n.succ ≤ n.succ +1 := by simp
      _ = n.succ.succ := by simp
      _ ≤ Ω.card :=h.right
    let p6:=arrangCardEqA Ω ⟨p1,p2⟩ 
    set a:=Ω.arrang ⟨p1,p2⟩ 
    have p3:=calc
      n.succ <n.succ +1 := by simp
      _ = n.succ.succ := by simp
      _ ≤ _ :=h.right
    let p4:= arrangCardEqA.aux p3 a
    set aSucc':=(Arrang.succ Ω p3 a)
    have p5:(Ω.arrang h)=aSucc' :=arrangUnique
    rw [p5.symm] at p4;rw [p4,p6];
    have p7:=calc
      Ω.card -n.succ.succ = Ω.card - (n.succ +1)  := by simp
      _ = Ω.card - n.succ -1 := by simp [Nat.sub_sub]
    let p8:=Nat.sub_le_sub_right h.right n.succ 
    replace p8:=calc 
      1 = n.succ.succ -n.succ := by simp
      _ ≤ _ := p8
    replace p8:=NAT.natSubtractAdd p8
    rw [p7.symm] at p8;rw [p8.symm,Nat.factorial_succ];
    rw [mul_comm (Ω.card -n.succ.succ +1)]
    rw [← Nat.div_div_eq_div_mul]
    have p9 :(Ω.card - n.succ.succ + 1)∣(Ω.card)!/(Ω.card-n.succ.succ)! := by
      have p10:Ω.card-n.succ.succ≤Ω.card := by simp
      replace p10:=factorial_dvd_factorial p10
      apply (dvd_div_iff p10).mpr
      rw [mul_comm];rw [← factorial_succ] 
      replace p8:=calc 
        (Finset.card Ω - succ (succ n)).succ =Finset.card Ω - succ (succ n) + 1
            := by simp
        _ = _ := p8
      rw [p8]
      have p11:Ω.card -n.succ ≤ Ω.card := by simp
      exact factorial_dvd_factorial p11
    rw [Nat.div_mul_cancel p9] 

end  CombinatorialNum

namespace Finset

open LIST FINSET

noncomputable def combin (Ω:Finset α) {kk:Nat} (h:(1≤kk)∧(kk≤Ω.card)):CombinatorialNum.Combin Ω kk:= by
  let a:=Ω.arrang h
  set combinL:List (Finset ↑Ω.toSet) 
    := a.arrang.toList.toSubtype.map (fun (x:ListSubtype a.arrang.toList) =>
      ⟨x.val,(a.nodup_len_n (Finset.mem_toList.mp x.property)).left ⟩ ) with HH1
  set combin:Finset (Finset (↑ Ω.toSet)):=⟨combinL.dedup,List.nodup_dedup _ ⟩ 
  have card_eq_n: ∀{s}, s∈combin -> s.card=kk := by 
    intro s H1
    have p1:s∈combinL := by simp_all
    replace p1:=LIST.listMemMapIff.mp p1
    exact Exists.elim p1 (by 
      intro x H2
      have p2:s.card=x.val.length := by 
        rw [H2.right.symm];simp
      let p3:= (a.nodup_len_n (Finset.mem_toList.mp x.property)).right
      rw [p2,p3]
    )
  have all_is_in: ∀{s:Finset (↑ Ω.toSet)}, (h: s.card=kk)->s∈combin := by
    intro s H1
    let p1:=Finset.mem_toList.mpr (a.all_is_in 
      ⟨FINSET.finsetToListNodup s,(H1 ▸ Finset.length_toList s)⟩ )
    exact Exists.elim ((@listMemIff _ _ a.arrang.toList).mp p1) (by
      intro n H2
      exact Exists.elim H2 ( by 
        intro H2 H3 
        let p2:=toSubtypeNEqOrigN a.arrang.toList H2
        rw [H3] at p2             
        have p3: n<a.arrang.toList.toSubtype.length := by 
          rw [ toSubtypeLenEqOrig];simp_all
        let p4:=listMapNEqFN (a.arrang.toList.toSubtype) 
          (fun (x:ListSubtype a.arrang.toList) =>( ⟨x.val,(a.nodup_len_n 
            (Finset.mem_toList.mp x.property)).left ⟩:(Finset ↑Ω.toSet) ) ) p3
        simp_rw [p2,← HH1] at p4
        have p5:n<combinL.length := by simp_all
        replace p5:=listGetIsMem p5; rw [p4] at p5
        let p6:=List.mem_dedup.mpr p5 
        have p7: s = ⟨ ↑(toList s), finsetToListNodup s⟩ :=calc 
          s = s.toList.toFinset  := by rw [Finset.toList_toFinset]
          _ = ⟨ ↑(toList s), finsetToListNodup s⟩   := by simp
        apply Finset.mem_val.mp
        rw [p7.symm] at p6 ;exact p6
    ))
  exact ⟨h,combin,card_eq_n,all_is_in ⟩ 
    
end Finset

namespace CombinatorialNum

open FINSET LIST Nat

set_option maxHeartbeats 800000
theorem combinCardEqC {n:Nat} (Ω:Finset α) (h:(1≤n)∧(n≤Ω.card)):
(Ω.combin h).combin.card = C(Ω.card,n) := by
  have inst:(Fintype (Subtype (arrang Ω h).arrang.toSet) ):= 
    ⟨(arrang Ω h).arrang.toSubtype,fun x=>toSubtypeMemMpr _ x.property ⟩ 
  set f:=(fun (x: (Finset (↑ Ω.toSet)))   =>
    let s:Set (↑ (Ω.arrang h).arrang.toSet):= fun y=>
      (⟨↑ (y.val), Multiset.coe_nodup.mpr ((Ω.arrang h).nodup_len_n y.property).left⟩)
        =x
    @Set.toFinset _ s (@Subtype.fintype _ s _ inst)
    ) 
  set combinL:List (Finset _) :=(Ω.combin h).combin.toList.map f 
    with HH1
  have p2:combinL.length=(Ω.combin h).combin.toList.length
        := by simp
  have p1:∀{i j:ℕ}(h1:i<combinL.length) (h2:j<combinL.length), i≠j 
    → combinL[i] ∩ combinL[j] = ∅ := by  
    intro i j h1 h2 h3
    by_contra hc ;
    exact Exists.elim (finsetNonEmptyMpr hc) (by 
      intro e H1
      rw [p2] at h1 h2
      have p3:= (listNodupIff.mp 
        (finsetToListNodup ((Ω.combin h).combin))) h1 h2 h3
      replace H1:= Finset.mem_inter.mp H1 
      let p4:=listMapNEqFN (Ω.combin h).combin.toList f h1
      let p5:=listMapNEqFN (Ω.combin h).combin.toList f h2
      simp_rw [←HH1] at p4 p5
      rw [p4,p5] at H1;simp at H1;
      set e1':= (Finset.toList (combin Ω h).combin)[i] 
      set e2':= (Finset.toList (combin Ω h).combin)[j] 
      set s1':Set (↑ (Ω.arrang h).arrang.toSet) :=
        fun y => 
          ⟨↑ (y.val), Multiset.coe_nodup.mpr ((Ω.arrang h).nodup_len_n y.property).left⟩
          = e1'
      set s2':Set (↑ (Ω.arrang h).arrang.toSet) :=
        fun y => 
          ⟨↑ (y.val), Multiset.coe_nodup.mpr ((Ω.arrang h).nodup_len_n y.property).left⟩
          = e2' 
      have H1_1:e∈ (@Set.toFinset _ s1' (@Subtype.fintype _ s1' _ inst)):=by
        exact H1.left
      replace H1_1
        :=(@Set.mem_toFinset _ s1' (@Subtype.fintype _ s1' _ inst) _).mp H1_1
      have H1_2:e∈ (@Set.toFinset _ s2' (@Subtype.fintype _ s2' _ inst)):=by
        exact H1.right
      replace H1_2
        :=(@Set.mem_toFinset _ s2' (@Subtype.fintype _ s2' _ inst) _).mp H1_2
      simp [Set.mem_def] at H1_1 H1_2
      let p6:= H1_1 ▸ H1_2
      simp at p3
      exact p3 p6)
  have p3: ∀{i:Nat},(h:i<combinL.length)-> combinL[i].card= (n !)  := by
    intro i h1
    rw [p2] at h1
    let p4:=listMapNEqFN (Ω.combin h).combin.toList f h1
    simp_rw [← HH1] at p4;
    set e:Finset Ω.toSet:=(((Ω.combin h).combin).toList)[i] with HH4
    set s:Set (Subtype (Ω.arrang h).arrang.toSet):= fun y=>
      (⟨↑ (y.val), Multiset.coe_nodup.mpr ((Ω.arrang h).nodup_len_n y.property).left⟩
        = e ) 
    set elist':=e.toList.map (fun x => x.val) with HH3
    have p5:elist'.Nodup := by 
      apply listNodupIff.mpr
      intro j k h3 h4 h5
      have p6:elist'.length = e.toList.length := by simp
      rw [p6] at h3 h4
      let p7:=listNodupIff.mp 
        (finsetToListNodup e) h3 h4 h5
      let p8:= listMapNEqFN e.toList (fun x=> x.val) h3
      let p9:= listMapNEqFN e.toList (fun x=> x.val) h4
      by_contra hc
      simp_rw [←HH3] at p8 p9
      rw [p8,p9] at hc
      simp_rw [←HH4] at hc
      exact (SET.SubtypeNeq p7) hc
    replace p5: ((↑elist') :Multiset _).Nodup := Multiset.coe_nodup.mpr p5
    let e':Finset _ := ⟨↑ elist',p5⟩ 
    set fs:=@Set.toFinset _ s (@Subtype.fintype _ s _ inst) with HH10
    replace p4:combinL[i]=fs := by
      rw [HH10];exact p4
    rw [p4]
    have p6:e'.card =e.card := by simp
    let p7:=(Ω.combin h).card_eq_n
      ( Finset.mem_toList.mp (listGetIsMem h1))
    rw [p6.symm] at p7;
    have h2: (1≤e'.card) ∧ (e'.card≤e'.card) := 
      ⟨p7.symm ▸ h.left,(by simp) ⟩ 
    have p8:e'⊆Ω := by
      apply Finset.subset_iff.mpr
      intro x h3
      have p9:x∈elist' := by simp_all
      exact Exists.elim (listMemMapIff.mp p9) (by
        intro b h4
        let p10:=h4.right ▸ b.property
        simp at p10
        exact p10)
    set f:ListSubtype (e'.arrang h2).arrang.toList -> 
    (Subtype (Ω.arrang h).arrang.toSet):=(fun (x) =>
        let p9:=(e'.arrang h2).nodup_len_n
          (Finset.mem_toList.mp x.property)
        let xval':List (Subtype Ω.toSet):=x.val.map (fun y
          => ⟨y.val,(Finset.subset_iff.mp p8) y.property ⟩ ) 
        have p11:xval'.length=x.val.length := by simp
        have p10:xval'.Nodup:= by
          apply listNodupIff.mpr
          intro i' j' h1' h2' h3'
          by_contra hc
          rw [p11] at h1' h2'
          have p12:=listMapNEqFN x.val (fun y
            => (⟨y.val,(Finset.subset_iff.mp p8) y.property ⟩:(Subtype Ω.toSet)) ) h1'
          have p13:=listMapNEqFN x.val (fun y
            => (⟨y.val,(Finset.subset_iff.mp p8) y.property ⟩:(Subtype Ω.toSet)) ) h2' 
          rw [p12,p13] at hc;
          replace hc:=congrArg Subtype.val hc
          simp at hc
          let p14:=(listNodupIff.mp p9.left) h1' h2' h3'
          exact (SubtypeNeq p14) hc
        ⟨xval' ,(Ω.arrang h).all_is_in ⟨p10, p7 ▸ (p9.right ▸ p11)⟩ ⟩ )
    set eAlist:List (Subtype (Ω.arrang h).arrang.toSet):=
      (e'.arrang h2).arrang.toList.toSubtype.map f with HH5
    let f':(Subtype e'.toSet)->(Subtype Ω.toSet):=
            fun y => ⟨y.val,(Finset.subset_iff.mp p8) y.property ⟩ 
    have p9:eAlist.Nodup := by 
      apply listNodupIff.mpr
      intro i' j' h1' h2' h3'
      have p10:eAlist.length = (e'.arrang h2).arrang.toList.toSubtype.length
        := by simp
      have p11:=(toSubtypeLenEqOrig (e'.arrang h2).arrang.toList )
      rw [p10] at h1' h2' 
      let p12:=listMapNEqFN (arrang e' h2).arrang.toList.toSubtype f h1' 
      let p13:=listMapNEqFN (arrang e' h2).arrang.toList.toSubtype f h2'
      by_contra hc
      have p14:= calc 
        _ = _ := p12.symm
        _ = _ := hc
        _ = _ := p13
      have p15:= (listNodupIff.mp
        (finsetToListNodup  (arrang e' h2).arrang)) (p11▸h1') (p11▸h2') h3'
      have p16 {A B :ListSubtype (e'.arrang h2).arrang.toList}:
        f A = f B -> A.val = B.val := by 
        intro  h1'
        simp at h1'
        let p17:=listEqIff.mp h1'
        apply listEqIff.mpr
        let p18:= p17.left;simp at p18
        have p19:∀{n:ℕ}(h1:n<A.val.length){h2:n<B.val.length},
        A.val[n] = B.val[n] := by
          intro kk h1'' h2''
          let p20:=listMapNEqFN A.val f' h1''
          let p21:=listMapNEqFN B.val f' h2''
          have p22:A.val.length = (A.val.map f').length := by simp
          have p23:B.val.length = (B.val.map f').length := by simp
          let p24:∀ {kk: ℕ} (h1:kk <(A.val.map f').length)(h2:kk<(B.val.map f').length)
            ,(A.val.map f')[kk] =(B.val.map f')[kk] :=(p17.right) 
          replace p24:= p24 (p22▸h1'') (p23▸h2'')
          rw [p20,p21] at p24
          have p25 {A' B' :Subtype e'.toSet}:(f' A' = f' B') -> A'=B' := by
            intro hh''
            simp at hh''
            calc 
              A' = ⟨A'.val,A'.property ⟩ :=rfl 
              _ = ⟨B'.val,B'.property ⟩ := by simp_rw [hh'']
          exact p25 p24
        exact ⟨p18,p19⟩ 
      replace p14:=p16 p14
      rw [p11] at h1' h2'
      rw [toSubtypeNEqOrigN (e'.arrang h2).arrang.toList h1'] at p14
      rw [toSubtypeNEqOrigN (e'.arrang h2).arrang.toList h2'] at p14
      exact p15 p14
    let eA:Finset _ :=⟨↑ eAlist,Multiset.coe_nodup.mpr p9⟩ 
    have p10: fs⊆eA := by 
      apply Finset.subset_iff.mpr
      intro x h3
      simp  at h3; 
      replace h3:=(@Set.mem_toFinset _ s ((@Subtype.fintype _ s _ inst)) _).mp  h3
      have p11 {z:Subtype Ω.toSet}:(z∈x.val)->(z.val∈e'):= by
        intro h4
        have p12:=calc
          e = _ :=HH4
          _ = _ :=h3.symm
        have p13:z∈e:=by
          rw [p12]
          exact Finset.mem_mk.mpr (Multiset.mem_coe.mpr h4)
        exact listMemMapMpr (fun u=> u.val) (Finset.mem_toList.mpr p13)
      let g:ListSubtype (x.val)->(Subtype e'.toSet) := 
        fun y =>
        ⟨y.val,p11 y.property ⟩ 
      have pg {t:ListSubtype (x.val)}: (g t).val =t.val := by rfl
      set x':=x.val.toSubtype.map g 
      have p12:x'.length=x.val.length := by simp[toSubtypeLenEqOrig]
      let p13:=( (Ω.arrang h).nodup_len_n x.property)
      have p14:x'.Nodup := by
        apply listNodupIff.mpr
        intro i' j' h1' h2' h3'
        rw [p12] at h1' h2'
        have h1'':=h1'
        have h2'':=h2'
        rw [← toSubtypeLenEqOrig] at h1' h2'
        let p16:=listMapNEqFN x.val.toSubtype g h1'
        let p17:=listMapNEqFN x.val.toSubtype g h2'
        rw [p16,p17];
        by_contra hc
        let p18:=listNodupIff.mp (p13.left) h1'' h2'' h3'
        replace hc := congrArg Subtype.val hc
        rw [@pg (x.val.toSubtype[i']),@pg (x.val.toSubtype[j'])] at hc
        rw [toSubtypeNEqOrigN,toSubtypeNEqOrigN] at hc
        exact (SubtypeNeq p18) hc
      have p15:(x.val.toSubtype.map g).map f' = x.val := by 
        apply listEqIff.mpr
        have p17:((x.val.toSubtype.map g).map f').length = x.val.length 
          := by simp [toSubtypeLenEqOrig]
        have p18: ∀{kk:ℕ}
          (h1:kk<((x.val.toSubtype.map g).map f').length) 
          {h2 : kk <(x.val.length)},
          ((x.val.toSubtype.map g).map f')[kk] = (x.val)[kk] := by
          intro kk h1' h2' 
          have p19:((x.val.toSubtype.map g).map f').length
            =(x.val.toSubtype.map g).length := by simp
          rw [p19] at h1'
          let p20:=listMapNEqFN (x.val.toSubtype.map g) f' h1'
          rw [p20]
          replace p19:(x.val.toSubtype.map g).length=x.val.toSubtype.length
          := by simp
          rw [p19] at h1'
          replace p20:=listMapNEqFN (x.val.toSubtype) g h1'
          rw [p20]
          simp; rw [toSubtypeLenEqOrig] at h1' 
          let p21:=toSubtypeNEqOrigN x.val h1'
          calc 
            _ = ((x.val.toSubtype)[kk]).val :=rfl
            _ = _ := p21
            _ = _ :=rfl
        exact ⟨p17,p18⟩ 
      let p16:=listMemIff.mp (Finset.mem_toList.mpr
        ((e'.arrang h2).all_is_in ⟨p14, p7.symm▸(p13.right▸p12)⟩ ))
      exact Exists.elim p16 ( by
        intro k h4'
        exact Exists.elim h4' (by
          intro h4 h5
          have p18:=toSubtypeLenEqOrig (e'.arrang h2).arrang.toList
          rw [p18.symm] at h4
          have p19:= (listMapNEqFN _ f h4)
          have p20: (e'.arrang h2).arrang.toList.toSubtype.length =
            ((e'.arrang h2).arrang.toList.toSubtype.map f).length := by simp
          rw [p20] at h4
          replace p19:=p19 ▸ (listGetIsMem h4)
          rw [←HH5] at p19
          have p21 {A :ListSubtype (e'.arrang h2).arrang.toList}:
            (f A).val = A.val.map f' := by rfl
          have p22: (f (arrang e' h2).arrang.toList.toSubtype[k]).val=x.val := by
            rw [p21,toSubtypeNEqOrigN,h5];exact p15
          have p23 {β:Type u_1 }{ss:Set β}{A' B' :Subtype ss}:
          A'.val = B'.val -> A' = B' := by
            intro h6;
            calc 
              A' = ⟨A'.val, _⟩ :=rfl  
              _ = ⟨B'.val, _ ⟩  := by simp_rw [h6]
          replace p22:=p23 p22 
          rw [p22.symm]; exact p19
        ))
    have p11:eA⊆fs := by  
      apply Finset.subset_iff.mpr
      intro x h3
      simp; 
      let lhsNd:=((Ω.arrang h).nodup_len_n x.property).left
      let lhs:= ({val:=↑ (x.val),nodup:=Multiset.coe_nodup.mpr lhsNd}: Finset _)
      let p13:= listMemMapIff.mp
        (Multiset.mem_coe.mp (Finset.mem_mk.mp h3  ))
      exact Exists.elim p13 ( by
        intro x' h4
        exact Exists.elim (listMemIff.mp h4.left) (by
          intro k h5
          exact Exists.elim h5 (by   
            intro h5 h6
            have p15 {B1:ListSubtype (e'.arrang h2).arrang.toList }:
            (f B1).val = B1.val.map f' := rfl
            replace h6:=congrArg (ListSubtype.val) h6
            let h5':=h5; rw [toSubtypeLenEqOrig] at h5'
            rw [toSubtypeNEqOrigN (arrang e' h2).arrang.toList h5'] at h6
            have p16:lhs ⊆ e := by 
              apply Finset.subset_iff.mpr
              intro z h7
              let p17:=p15▸(congrArg (Subtype.val) h4.right)
              replace h7:=listMemMapIff.mp
                (p17.symm ▸ (Multiset.mem_coe.mp (Finset.mem_mk.mp h7)))
              exact Exists.elim h7 ( by 
                intro z' h8
                exact Exists.elim (listMemMapIff.mp (Multiset.mem_coe.mp 
                  (Finset.mem_mk.mp (z'.property:z'.val∈e')))) (by 
                    intro  z'' h9
                    let p18:=Finset.mem_toList.mp h9.left
                    replace h8:=congrArg (Subtype.val) h8.right;
                    simp at h8; rw [h9.right.symm] at h8
                    have p19:z''=z:=calc 
                      z'' = ⟨z''.val ,_⟩ :=rfl 
                      _ = ⟨z.val,_ ⟩:= by simp_rw [h8] 
                    exact p19 ▸ p18  ))
            have p17: e⊆lhs := by
              apply Finset.subset_iff.mpr
              intro z h7
              have p17:=p15▸(congrArg (Subtype.val) h4.right)
              rw [toSubtypeLenEqOrig] at h5
              let ll:=(Finset.toList (arrang e' h2).arrang)
              have HH9:ll=(Finset.toList (arrang e' h2).arrang) := rfl
              simp_rw [←HH9] at h5 h6
              let p18:=(arrang e' h2).nodup_len_n 
                (Finset.mem_toList.mp (listMemIff.mpr ⟨_,h5,h6⟩ ))
              let xvalSlist:=x'.val.map (fun z=>z.val)
              have p19:xvalSlist.length=e'.card := by
                rw [p18.right.symm];simp
              have p20:xvalSlist.Nodup := by 
                apply listNodupIff.mpr
                intro i' j' h1' h2' h3'
                have p21:xvalSlist.length = x'.val.length := by simp
                rw [p21] at h1' h2'
                let p22:=listNodupIff.mp (p18.left) h1' h2' h3'
                let p23:=listMapNEqFN _ (fun z=>z.val) h1'
                let p24:=listMapNEqFN _ (fun z=>z.val) h2'
                rw [p23,p24];replace p22:=SubtypeNeq p22
                exact p22
              let xvalS:Finset _ := ⟨↑xvalSlist,Multiset.coe_nodup.mpr p20⟩ 
              have p21:xvalS = e' := by  
                have p22:xvalS.card≥e'.card := calc 
                  _ = xvalSlist.length := by simp
                  _ = e'.card := p19
                  _ ≥ _ := by simp
                have p23 : xvalS ⊆ e' := by
                  apply Finset.subset_iff.mpr
                  intro w h8
                  exact Exists.elim (listMemMapIff.mp
                    (Multiset.mem_coe.mp (Finset.mem_mk.mp h8))) (by
                      intro w' h9
                      exact (h9.right ▸ w'.property))
                exact Finset.eq_of_subset_of_card_le p23 p22
              replace h7:z.val ∈e'
                := Finset.mem_mk.mpr (
                  (listMemMapMpr (fun w=>w.val) (Finset.mem_toList.mpr h7)))
              exact Exists.elim (listMemMapIff.mp  (Multiset.mem_coe.mp
                (Finset.mem_mk.mp (p21.symm ▸ h7)))) (by 
                  intro z' h8
                  let p22:f' z' ∈ lhs:=  Finset.mem_mk.mpr ( Multiset.mem_coe.mpr
                    (p17 ▸ (listMemMapMpr f' h8.left)))
                  have p23: (f' z').val = z.val := by simp; exact h8.right
                  have p24 {β:Type u_1 }{ss:Set β}{A' B' :Subtype ss}:
                    A'.val = B'.val -> A' = B' := by
                    intro h9;
                    calc 
                      A' = ⟨A'.val, _⟩ :=rfl  
                      _ = ⟨B'.val, _ ⟩  := by simp_rw [h9]
                  replace p24:=p24 p23
                  exact p24 ▸ p22)
            apply (@Set.mem_toFinset _ s ((@Subtype.fintype _ s _ inst)) _).mpr  
            exact (Finset.Subset.antisymm p16 p17)
              )))
    let p12:= congrArg Finset.card
      (Finset.Subset.antisymm p10 p11)
    have p13:eA.card = eAlist.length := by simp
    have p14:eAlist.length = (e'.arrang h2).arrang.toList.toSubtype.length
      := by simp
    rw [toSubtypeLenEqOrig,Finset.length_toList] at p14
    let p15:=arrangCardEqA e' h2; simp_rw [p7] at p15
    simp at p15
    exact (p12.symm ▸ (p13.symm ▸ (p15 ▸ p14)))
  let combinA:=combinL.foldr (.∪.) ∅
  have p4:∀{s' : Finset _}, s'∈combinL → s'⊆(arrang Ω h).arrang.toSubtype := by
      intro s' _
      apply Finset.subset_iff.mpr
      intro y _
      exact toSubtypeMemMpr _ y.property
  let p5:=finsetUnionOfDisjoint combinL 
       (arrang Ω h).arrang.toSubtype p4 p1
  let p5_1:=p5.left
  let p5_2:=p5.right.left
  have p6:(Ω.arrang h).arrang.toSubtype ⊆combinA := by
    apply Finset.subset_iff.mpr 
    intro x _
    let p7:=(arrang Ω h).nodup_len_n x.property
    set xS:Finset (Subtype Ω.toSet)
      := ⟨⟦x.val⟧,Multiset.coe_nodup.mpr p7.left ⟩  
    have p8:xS.card=n := by simp;exact p7.right
    replace p8: f xS ∈ combinL:= listMemMapMpr f (Finset.mem_toList.mpr
      ((Ω.combin h).all_is_in p8))
    set s':Set (Subtype (Ω.arrang h).arrang.toSet):= (fun y=>
      (⟨⟦y.val⟧, Multiset.coe_nodup.mpr ((Ω.arrang h).nodup_len_n y.property).left⟩
        = xS)) 
    have p9: x∈s'-> x∈(@Set.toFinset _ s' (@Subtype.fintype _ s' _ inst))
      := (@Set.mem_toFinset _ s' (@Subtype.fintype _ s' _ inst) x ).mpr
    have p10:x ∈ f xS := by 
      simp
      simp_rw [← Multiset.quot_mk_to_coe]
      apply p9; apply Set.mem_def.mpr
      rfl
    exact (p5.right.right.mpr ⟨f xS,p8,p10 ⟩ )
  replace p6:combinA = (Ω.arrang h).arrang.toSubtype
    :=Finset.Subset.antisymm p5_1 p6
  replace p6:=congrArg (Finset.card) p6
  rw [toSubtypeCardEqOrig] at p6
  replace p5_2:combinA.card = (combinL).foldr (fun x v=>x.card+v) 0:= calc 
    combinA.card = (combinL.map Finset.card).foldr (.+.) 0 := p5_2
    _ = combinL.foldr (fun x v=>x.card+v) 0 := by rw [List.foldr_map]
  have p3':∀ {w}, w ∈ combinL → w.card = n !:= by 
    intro w h2
    exact Exists.elim (listMemIff.mp h2) (by
      intro k h3
      exact Exists.elim h3 ( by
        intro h3 h4
        rw [h4.symm];exact p3 h3))
  let p7:=meaningOfMultip p3'
  rw [p7,p6] at p5_2 ; rw [Finset.length_toList] at p2
  rw [p2] at p5_2
  let p8:= arrangCardEqA Ω h
  rw [p8] at p5_2;simp
  replace p5_2:=congrArg (./n !) p5_2
  simp at p5_2 ;rw [mul_comm] at p5_2
  let p9:=Nat.mul_div_cancel (combin Ω h).combin.card (factorial_pos n)
  exact (p9▸p5_2).symm

set_option maxHeartbeats 200000

theorem combinUnique {Ω:Finset α} {c1 c2:Combin Ω n} : c1=c2 := by    
  have p1: c1.combin=c2.combin := by
    apply Finset.ext_iff.mpr
    intro t
    have mp:t∈c1.combin -> t∈c2.combin := by
      intro h
      exact c2.all_is_in (c1.card_eq_n h)
    have mpr:t∈c2.combin -> t∈c1.combin := by
      intro h
      exact c1.all_is_in (c2.card_eq_n h)
    exact ⟨mp,mpr⟩
  calc
    c1 = ⟨_,c1.combin,_,_⟩ := rfl  
    _ = ⟨_,c2.combin,_,_⟩ := by simp_rw[p1] 

end CombinatorialNum

