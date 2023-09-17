import Mathlib.Data.Real.Basic
import GradMath.Basic.Basic

noncomputable section

namespace RAT

lemma ratBetweenAnyReals {x y:Real} (h:x<y) :∃q:ℚ, x<q ∧ q<y := by
  by_cases c:4 < (y-x) 
  case pos =>
    refine' Exists.elim (Real.exists_floor x) _
    intro q' hq'
    have p1:x< q'+1 := by
      by_contra hc; push_neg at hc
      let p2:=hq'.right (q'+1) (by simp;exact hc)
      simp at p2
    have p2: q'+1<y := by
      have p3: (↑1:Real) < (↑4:Real) := by 
        let p4:(1:ℚ ) <4 := by simp
        let p5:= (@Real.ratCast_lt (1:ℚ) (4:ℚ)).mpr  p4
        simp at p5; exact p5
      replace c:= REAL.leAddLt (by simp:x≤x) c
      simp at c
      calc 
        q'+1 ≤ x +1 := by simp ;exact hq'.left
        _ < x+4 := by simp [p3] ; 
        _ < y := c
    exact ⟨(q'+1),by simp; exact p1,by simp; exact p2⟩ 
  case neg =>
    refine' Exists.elim (Real.exists_floor  (4/(y-x)) ) _
    intro r hr; push_neg at c
    refine' Exists.elim (Real.exists_floor  (x*(r+1)) ) _
    intro x' hx'
    refine' Exists.elim (Real.exists_floor  (y*(r+1)) ) _
    intro y' _
    have p0: 0< (y-x) := by simp [h]
    let q:ℚ := ((x'+1):ℚ)/((r + 1):ℚ)
    have p1: x < q := by
      have p2:x*(↑r + 1) < ↑x' + 1 :=by
        by_contra hc; push_neg at hc
        let p2:=hx'.right (x'+1) (by simp;exact hc)
        simp at p2
      have p3:0 < (↑r:Real) + 1:= by 
        replace p0:=calc
          0 < 1/ (y - x) *4 :=by simp; exact h
          _ = 4/(y - x) := by ring
        let p5:=hr.right 0 (by simp;exact p0.le)
        calc 
          (0:ℝ) ≤ r := by simp; exact p5
          _ < (r:ℚ) + 1 := by simp
      let p4:(0 :Real)< (1 / (↑r + 1)):=by 
        simp; exact p3
      calc 
        x = x * (↑r + 1) * (1 / (↑r + 1)) :=by 
              simp; rw [mul_assoc,Field.mul_inv_cancel _ p3.ne.symm]; simp
        _ < _ := REAL.mulPosLtMulPosMpr p2 p4
        _ = ↑q := by simp [Field.div_eq_mul_inv]
    have p2:q<y := by
      have p3: (4:Real) / (y - x) <r+1 := by
        by_contra hc; push_neg at hc
        let p4:=hr.right (r+1) (by simp;exact hc)
        simp at p4
      replace p3:=REAL.mulPosLtMulPosMpr p3 p0
      rw [Field.div_eq_mul_inv,mul_assoc,@mul_comm _ _ ((y - x)⁻¹)] at p3
      let p4:=@Field.mul_inv_cancel _ _ _ p0.ne.symm
      rw [p4,sub_eq_add_neg,left_distrib] at p3;simp at p3
      have p5: (↑1:Real) < (↑4:Real) := by 
        let p6:(1:ℚ ) <4 := by simp
        let p7:= (@Real.ratCast_lt (1:ℚ) (4:ℚ)).mpr  p6
        simp at p7; exact p7
      replace p5:= calc
        x'+1 ≤ x * (↑r + 1) +1 := by simp; exact hx'.left
        _ < 4 + (↑r + 1) * x := by rw [add_comm,mul_comm]; simp; exact p5
        _ < _ := p3
      have p6:0 < (↑r:Real) + 1:= by 
        replace p0:=calc
          0 < 1/ (y - x) *4 :=by simp; exact h
          _ = 4/(y - x) := by ring
        let p5:=hr.right 0 (by simp;exact p0.le)
        calc 
          (0:ℝ) ≤ r := by simp; exact p5
          _ < (r:ℚ) + 1 := by simp
      replace p5:=REAL.mulPosLtMulPosMpr p5 (REAL.posInvIsPos p6)
      have p7:((r:Real )+ 1)⁻¹ * ((r:Real) + 1) = 1 := by
        rw [mul_comm,Field.mul_inv_cancel ]; exact p6.ne.symm
      calc 
        ↑q = (↑x' + 1) * (1 / ((r:Real )+ 1)) := by simp ;rw [Field.div_eq_mul_inv]
        _ < _ := p5
        _ = y:=by simp; rw [mul_assoc,mul_comm,mul_assoc,p7];simp
    exact ⟨_,p1,p2⟩ 
