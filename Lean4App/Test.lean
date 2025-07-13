import Mathlib.Data.Polynomial.Basic
import Mathlib.Algebra.Field.Basic

/-!
# 簡單測試文件

這個文件包含一些基本的測試來驗證項目是否正常工作。
-/

-- 測試1: 基本多項式運算
def test_polynomial : Polynomial ℝ :=
  Polynomial.X ^ 2 + Polynomial.C 1

theorem test_polynomial_degree : test_polynomial.degree = 2 := by
  unfold test_polynomial
  rw [Polynomial.degree_add_eq_left_of_degree_lt]
  · rw [Polynomial.degree_pow, Polynomial.degree_X]
    simp
  · rw [Polynomial.degree_C]
    simp

-- 測試2: 多項式求值
theorem test_polynomial_eval : test_polynomial.eval 0 = 1 := by
  unfold test_polynomial
  simp [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]

-- 測試3: 代數基本定理的簡單應用
theorem test_fundamental_theorem {K : Type*} [Field K] [AlgebraicallyClosed K]
  (f : Polynomial K) (hf : f ≠ 0) (hdeg : f.degree > 0) :
  ∃ x : K, f.eval x = 0 := by
  exact Polynomial.exists_root hf

-- 測試4: 理想的基本性質
theorem test_ideal_property (a : ℝ) :
  a ∈ Ideal.span {a} := by
  exact Ideal.mem_span_singleton_self a

-- 測試5: 代數集的定義
def test_algebraic_set {K : Type*} [Field K] (f : Polynomial K) : Set K :=
  { x : K | f.eval x = 0 }

theorem test_algebraic_set_property {K : Type*} [Field K] (f : Polynomial K) (x : K) :
  x ∈ test_algebraic_set f ↔ f.eval x = 0 := by
  rfl 