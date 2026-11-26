module

public import New.UpperBound.Divisibility.MarkOperator
public import research.FrobeniusPairingCore

/-!
# A primitive coefficient row on a scaled Hecke image

Research wrapper for the readable proof at community commit `0d9138b2`.
The polynomial input is an ordinary monomial coefficient vector whose translates,
after the source's depth scaling, are coefficientwise divisible by `p`.
The conclusions below use the literal transposed edge matrix and the actual
integral source forms. This file does not enter the default proof build.
-/

@[expose] public section

noncomputable section

namespace New.FrobeniusRowResearch

open Matrix Finset FrobeniusCycle Gf Data ComplexConjugate WithZero NumberField

section CoordinateRow

variable {O E X I H : Type*} [CommRing O] [Fintype E]

/-- Read one class and one complementary coefficient using an ordinary polynomial row. -/
def coordinateRow (J : I ≃ E × H) (h : E → O) (x : X) (h₀ : H) :
    (X → I → O) →ₗ[O] O where
  toFun F := ∑ β : E, h β * F x (J.symm (β, h₀))
  map_add' F G := by simp [mul_add, sum_add_distrib]
  map_smul' a F := by simp [mul_sum, mul_left_comm]

@[simp]
lemma coordinateRow_apply (J : I ≃ E × H) (h : E → O) (x : X) (h₀ : H)
    (F : X → I → O) :
    coordinateRow J h x h₀ F = ∑ β : E, h β * F x (J.symm (β, h₀)) := rfl

/-- A coefficient equal to one gives a standard integral vector read as one. -/
lemma coordinateRow_exists_unit (J : I ≃ E × H) (h : E → O) (x : X) (h₀ : H)
    (β₀ : E) (h_unit : h β₀ = 1) :
    ∃ F : X → I → O, coordinateRow J h x h₀ F = 1 := by
  classical
  refine ⟨Pi.single x (Pi.single (J.symm (β₀, h₀)) 1), ?_⟩
  simp [coordinateRow_apply, Pi.single_apply, h_unit]

end CoordinateRow

section EdgeRow

variable {N k n r : ℕ} {W O : Type} {X H I : Type*}
  [CommRing W] [IsLocalRing W] [CommRing O] [NeZero N]
  [Fintype (ParahoricCosets W k r)] [Fintype H] [DecidableEq H] [Fintype I]

/-- A deep ordinary coefficient column defines a row divisible by `p` on every
incoming edge of the literal scaled edge Hecke operator. -/
lemma coordinateRow_edgeHeckeOperator_dvd (T : FrobeniusCycle N W O)
    (J : I ≃ Exponents N k n × H) (𝓔 : EdgeCoordinates W O k r X H)
    (h : Exponents N k n → O)
    (h_deep : ∀ (g : GL (Fin k) W) (β : Exponents N k n),
      (T.p : O) ∣ (T.depthPower k n r *ᵥ (T.letterRep n g *ᵥ h)) β)
    (x : X) (h₀ : H) (F : X → I → O) :
    (T.p : O) ∣ coordinateRow J h x h₀ (T.edgeHeckeOperator n J 𝓔 F) := by
  classical
  have h_edge (b : ParahoricCosets W k r) (β : Exponents N k n) :
      (T.p : O) ∣
        ((T.letterRep n (𝓔.originBasisChange (x, b)) * T.depthPower k n r *
          T.letterRep n (𝓔.terminusBasisChange b)) *ᵥ h) β := by
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change (T.p : O) ∣ ∑ α : Exponents N k n,
      T.letterRep n (𝓔.originBasisChange (x, b)) β α *
        (T.depthPower k n r *ᵥ (T.letterRep n (𝓔.terminusBasisChange b) *ᵥ h)) α
    exact Finset.dvd_sum fun α _ ↦ dvd_mul_of_dvd_right (h_deep _ α) _
  rw [coordinateRow_apply, T.edgeHeckeOperator_apply]
  simp only [Equiv.apply_symm_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.dvd_sum
  intro b hb
  rw [Finset.sum_comm]
  apply Finset.dvd_sum
  intro j hj
  have h_rearrange :
      (∑ β : Exponents N k n, h β *
        (𝓔.transition (x, b) h₀ (J j).2 *
          (T.letterRep n (𝓔.originBasisChange (x, b)) * T.depthPower k n r *
            T.letterRep n (𝓔.terminusBasisChange b)) (J j).1 β *
          F (𝓔.origin (x, b)) j)) =
      𝓔.transition (x, b) h₀ (J j).2 *
        ((T.letterRep n (𝓔.originBasisChange (x, b)) * T.depthPower k n r *
          T.letterRep n (𝓔.terminusBasisChange b)) *ᵥ h) (J j).1 *
        F (𝓔.origin (x, b)) j := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro β hβ
    ring
  rw [h_rearrange]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (h_edge b (J j).1) _) _

end EdgeRow

section IntegralCoordinates

variable {P : Parameters} {D : Data P} {p : ℕ} [Fact p.Prime] [PadicPlace p]

/-- Evaluation at class representatives is a left inverse to the source's
integral-value constructor, so that constructor is injective. -/
lemma sourceFormOfValues_injective
    {ρ : StdClasses (D.levelX 0) → Gf D.E (D.X 0)}
    (hρ : ∀ x : StdClasses (D.levelX 0),
      DoubleCoset.mk stdRatPoints (D.levelX 0) (ρ x) = x) :
    Function.Injective (Columns.sourceFormOfValues (p := p) hρ) := by
  intro F G hFG
  funext x i
  apply Subtype.ext
  have h_eval := congrArg (fun φ : D.SourceForm ↦ φ.val.val (ρ x) i) hFG
  simpa only [Columns.sourceFormOfValues_apply_rep] using h_eval

/-- The source's integral coordinate constructor, with its actual image as codomain. -/
def integralSourceFormsEquiv
    {ρ : StdClasses (D.levelX 0) → Gf D.E (D.X 0)}
    (hρ : ∀ x : StdClasses (D.levelX 0),
      DoubleCoset.mk stdRatPoints (D.levelX 0) (ρ x) = x)
    (hρ_int : ∀ x : StdClasses (D.levelX 0), ρ x ∈ integralAbove (D.X 0) p) :
    (StdClasses (D.levelX 0) → WeylIndex (D.X 0) D.columnCount → embValRing)
      ≃ₗ[embValRing] D.integralSourceForms := by
  let f := Columns.sourceFormOfValues (p := p) hρ
  have hf_mem (F) : f F ∈ D.integralSourceForms := by
    rw [← Columns.range_sourceFormOfValues hρ hρ_int]
    exact ⟨F, rfl⟩
  exact LinearEquiv.ofBijective (f.codRestrict D.integralSourceForms hf_mem) ⟨
    fun F G h ↦ sourceFormOfValues_injective hρ (congrArg Subtype.val h),
    fun φ ↦ by
      have h_mem : φ.val ∈ f.range := by
        rw [Columns.range_sourceFormOfValues hρ hρ_int]
        exact φ.property
      obtain ⟨F, hF⟩ := h_mem
      exact ⟨F, Subtype.ext hF⟩⟩

@[simp]
lemma integralSourceFormsEquiv_coe
    {ρ : StdClasses (D.levelX 0) → Gf D.E (D.X 0)}
    (hρ : ∀ x : StdClasses (D.levelX 0),
      DoubleCoset.mk stdRatPoints (D.levelX 0) (ρ x) = x)
    (hρ_int : ∀ x : StdClasses (D.levelX 0), ρ x ∈ integralAbove (D.X 0) p)
    (F : StdClasses (D.levelX 0) → WeylIndex (D.X 0) D.columnCount → embValRing) :
    (integralSourceFormsEquiv hρ hρ_int F).val = Columns.sourceFormOfValues hρ F := rfl

end IntegralCoordinates

section Transport

variable {O V V' : Type*} [CommRing O]
  [AddCommGroup V] [Module O V] [AddCommGroup V'] [Module O V']

/-- Transfer a primitive image row through an actual lattice isomorphism. -/
lemma exists_primitive_row_of_equiv (M : Submodule O V') (e : V ≃ₗ[O] M)
    (Y : Module.End O V') (B : Module.End O V)
    (h_lift : ∀ F : V, Y (e F).val = (e (B F)).val)
    (p : O) (row : V →ₗ[O] O) (seed : V) (h_unit : row seed = 1)
    (h_dvd : ∀ F : V, p ∣ row (B F)) :
    ∃ (rowM : M →ₗ[O] O) (φ₀ : M), rowM φ₀ = 1 ∧
      ∀ φ : M, ∃ h_int : Y φ.val ∈ M, p ∣ rowM ⟨Y φ.val, h_int⟩ := by
  let rowM : M →ₗ[O] O := row.comp e.symm.toLinearMap
  refine ⟨rowM, e seed, by simpa [rowM] using h_unit, ?_⟩
  intro φ
  have h_val : Y φ.val = (e (B (e.symm φ))).val := by
    simpa using h_lift (e.symm φ)
  have h_int : Y φ.val ∈ M := h_val.symm ▸ (e (B (e.symm φ))).property
  refine ⟨h_int, ?_⟩
  have h_eq : (⟨Y φ.val, h_int⟩ : M) = e (B (e.symm φ)) := Subtype.ext h_val
  simpa [rowM, h_eq] using h_dvd (e.symm φ)

end Transport

open Columns

/-- The source's large-degree hypothesis already pays for one adjacent pairing. -/
lemma frobeniusPower_le_of_isLargeDegree
    {N k a r : ℕ} {W O : Type} [CommRing W] [IsLocalRing W] [CommRing O] [NeZero N]
    (T : FrobeniusCycle N W O) {θ : ℝ} (h_size : T.IsLargeDegree k a r θ) :
    T.P ≤ a := by
  have h_base : (1 : ℝ) ≤ N * k * Real.log T.q / θ := by
    have h_nk : (4 : ℝ) ≤ N * k := by exact_mod_cast h_size.four_le_mul
    have h_log : (27 : ℝ) ≤ Real.log T.q := h_size.twenty_seven_le_log_q
    have h_one : (1 : ℝ) ≤ N * k * Real.log T.q :=
      (by norm_num : (1 : ℝ) ≤ 4 * 27).trans
        (mul_le_mul h_nk h_log (by norm_num) (by positivity))
    exact h_one.trans h_size.mul_log_le_div
  have h_exp : 3 * r ≠ 0 := by have := h_size.block_pos; omega
  have h_pow : (T.P : ℝ) ≤ (T.P : ℝ) ^ (3 * r) := by
    exact_mod_cast Nat.le_self_pow h_exp T.P
  have h_factor : (T.P : ℝ) ^ (3 * r) ≤
      (N * k * Real.log T.q / θ) ^ 5 * (T.P : ℝ) ^ (3 * r) :=
    le_mul_of_one_le_left (by positivity) (one_le_pow₀ h_base)
  exact_mod_cast h_pow.trans (h_factor.trans h_size.le_degree)

/-- The actual scaled Hecke operator has a primitive integral separating row
whenever its Frobenius cycle has a primitive deep coefficient column.

The hypotheses identifying the cycle and the size conditions are exactly those
used by `Columns.isOntoUpToColength_scaledHeckeOperator_of_frobeniusCycle`.
The coordinate construction below follows that theorem, retaining the actual
normalization and the transpose in every incoming edge.
-/
theorem exists_primitive_row_scaledHeckeOperator_of_deep_coefficients
    {P : Parameters} {p : ℕ} {D : Data P} [Fact p.Prime] [PadicPlace p]
    {Λ : Finset (FinPlace D.E)} {l : FinPlace D.E} {N : ℕ}
    {W : ValuationSubring D.E} {θ : ℝ} {Q : D.Φ → Prop} [NeZero N]
    (hΛ : D.IsMarked Λ) (hlΛ : l ∈ Λ)
    (hW : W = (l.valuation D.E).valuationSubring) (T : FrobeniusCycle N W embValRing)
    (hTp : T.p = p) (t : ZMod N ≃ Subtype Q)
    (hQ : ∀ σ : D.Φ, Q σ ↔ σ ∈ D.aPlaces ∧
      (inducedPlace σ = l ∨ inducedPlace σ = star l))
    (hι : ∀ (i : ZMod N) (x : W),
      T.embedding i x = (if T.isEven i then Φ (t i).val else (Φ (t i)).comp conj) x)
    (h_exponent : heckeScalingExponent l = D.a * #{i : ZMod N | T.isEven i})
    (h_size : T.IsLargeDegree D.k D.a (D.ceilLogLifts p) θ)
    (h : Exponents N D.k D.a → embValRing)
    (h_deep : ∀ (g : GL (Fin D.k) W) (β : Exponents N D.k D.a),
      (T.p : embValRing) ∣
        (T.depthPower D.k D.a (D.ceilLogLifts p) *ᵥ (T.letterRep D.a g *ᵥ h)) β)
    (β₀ : Exponents N D.k D.a) (h_unit : h β₀ = 1) :
    ∃ (rowM : D.integralSourceForms →ₗ[embValRing] embValRing)
      (φ₀ : D.integralSourceForms), rowM φ₀ = 1 ∧
      ∀ φ : D.integralSourceForms,
        ∃ h_int : hΛ.scaledHeckeOperator ⟨l, hlΛ⟩ φ.val ∈ D.integralSourceForms,
          (p : embValRing) ∣ rowM ⟨hΛ.scaledHeckeOperator ⟨l, hlΛ⟩ φ.val, h_int⟩ := by
  classical
  subst hW
  set r : ℕ := D.ceilLogLifts p
  have hr : r < D.k := by linarith [h_size.block_pos, h_size.two_mul_block_le]
  have hl : l.IsSplit := hΛ.isSplit hlΛ
  have hp_val : l.valuation D.E p = exp (-1) := hΛ.valuation_natCast_eq_exp_neg_one hlΛ
  have hK : maxCompactAt (D.X 0) l ≤ D.levelX 0 := hΛ.maxCompactAt_le_levelX hlΛ
  have := T.finite_residueField
  have : Fintype (ParahoricCosets (valuationRingAt l) D.k r) := .ofFinite _
  have q : D.X 0 ≃ Fin D.k := Fintype.equivFinOfCardEq (by simp [D.card_X 0, Data.n])
  obtain ⟨C⟩ : Nonempty (HeckeEdges D.k p r (D.levelX 0) hl) :=
    nonempty_heckeEdges r (D.levelX 0) hl q (hΛ.natCast_mem_asIdeal hlΛ)
  have h_aPlace (i : ZMod N) : (t i).val ∈ D.aPlaces := ((hQ (t i)).1 (t i).2).1
  let H : Type := WeylIndex (D.X 0) fun τ : {τ : D.Φ // ¬Q τ} ↦ D.columnCount τ
  obtain ⟨J, hJ⟩ : ∃ J : WeylIndex (D.X 0) D.columnCount ≃ Exponents N D.k D.a × H,
      ∀ (c : ZMod N → ℂ) (z : D.Φ → Matrix (D.X 0) (D.X 0) ℂ)
        (i j : WeylIndex (D.X 0) D.columnCount),
        (∏ s : ZMod N, c s) ^ D.a * schur D.columnCount z i j =
          schur (fun τ : {τ : D.Φ // ¬Q τ} ↦ D.columnCount τ) (fun τ ↦ z τ)
            (J i).2 (J j).2 *
            kroneckerPi (fun s : ZMod N ↦
              symPowMatrix D.a
                (c s • (z (t s))ᵀ.submatrix C.numbering.symm C.numbering.symm))
              (J j).1 (J i).1 :=
    exists_weylIndex_equiv C.numbering t h_aPlace
  have h_off (e : ClassEdges (D.levelX 0) l D.k r) :
      ∃ m : GL H embValRing,
        schur (fun τ : {τ : D.Φ // ¬Q τ} ↦ D.columnCount τ)
          (fun τ ↦ (C.rationalPart e).val.val.map ((Φ τ.val).comp conj)) =
            m.val.map embValRing.subtype := by
    refine exists_schur_eq_map fun τ hτ hτQ ↦ ?_
    obtain ⟨h_ne, h_ne_star⟩ : inducedPlace τ ≠ l ∧ inducedPlace τ ≠ star l := by
      simpa [hQ, hτ] using hτQ
    exact C.localGL_rationalPart_mem_localIntGL e (by simpa using D.p_mem_inducedPlace τ)
      (star_involutive.eq_iff.not.2 h_ne_star) (by rwa [star_star])
  choose m hm using h_off
  let 𝓔 : EdgeCoordinates (valuationRingAt l) embValRing D.k r
      (StdClasses (D.levelX 0)) H :=
    { origin := C.origin
      originBasisChange := C.originBasisChange
      terminusBasisChange b := b.out⁻¹
      transition := m
      mk_terminusBasisChange_inv b := by rw [inv_inv, QuotientGroup.out_eq']
      eq_of_origin_eq := C.eq_of_origin_eq_of_mem_parahoric hp_val hK
        D.classAut_levelX_zero_eq_bot }
  let f : (StdClasses (D.levelX 0) → WeylIndex (D.X 0) D.columnCount → embValRing)
      →ₗ[embValRing] D.SourceForm := sourceFormOfValues C.mk_rep
  have h_edge (x : StdClasses (D.levelX 0))
      (b : ParahoricCosets (valuationRingAt l) D.k r)
      (i j : WeylIndex (D.X 0) D.columnCount) :
      (p : ℂ) ^ heckeScalingExponent l *
        schur D.columnCount (fun τ ↦ (C.rationalPart (x, b)).val.val.map ((Φ τ).comp conj)) i j =
        𝓔.transition (x, b) (J i).2 (J j).2 *
          (T.letterRep D.a (𝓔.originBasisChange (x, b)) * T.depthPower D.k D.a r *
            T.letterRep D.a (𝓔.terminusBasisChange b)) (J j).1 (J i).1 := by
    rw [h_exponent, pow_mul', ← prod_const, prod_filter, hJ, hm,
      kroneckerPi_symPowMatrix_eq_letterRep T hTp C.numbering D.a
        (fun i : ZMod N ↦ Φ (t i).val) hι (C.rationalPart_inv x b)]
    rfl
  have h_lift : hΛ.scaledHeckeOperator ⟨l, hlΛ⟩ ∘ₗ f =
      f ∘ₗ T.edgeHeckeOperator D.a J 𝓔 := by
    refine LinearMap.ext fun F ↦ levelSpace_ext_doubleCosets C.mk_rep fun x ↦ ?_
    change (p : ℂ) ^ heckeScalingExponent l •
        (heckeSplit (algFormRep D.columnCount (D.lastEntry 0)) hl r (f F).val).val (C.rep x) =
      (f (T.edgeHeckeOperator D.a J 𝓔 F)).val.val (C.rep x)
    have h_origin : C.origin = 𝓔.origin := rfl
    rw [C.heckeSplit_apply_rep hp_val hr hK (f F).2, sourceFormOfValues_apply_rep,
      edgeHeckeOperator_apply]
    ext i
    push_cast
    simp only [f, sourceFormOfValues_apply_rep, weightRep_column_apply, Pi.smul_apply,
      smul_eq_mul, Finset.sum_apply, mulVec, dotProduct, mul_sum, ← mul_assoc, h_edge, h_origin]
  let e := integralSourceFormsEquiv C.mk_rep C.rep_mem_integralAbove
  let x₀ : StdClasses (D.levelX 0) := DoubleCoset.mk stdRatPoints (D.levelX 0) 1
  let h₀ : H := Classical.choice inferInstance
  obtain ⟨seed, h_seed⟩ := coordinateRow_exists_unit J h x₀ h₀ β₀ h_unit
  refine exists_primitive_row_of_equiv D.integralSourceForms e
    (hΛ.scaledHeckeOperator ⟨l, hlΛ⟩) (T.edgeHeckeOperator D.a J 𝓔)
    (fun F ↦ ?_) (p : embValRing) (coordinateRow J h x₀ h₀) seed h_seed (fun F ↦ ?_)
  · simpa only [e, integralSourceFormsEquiv_coe, f, LinearMap.comp_apply] using
      LinearMap.congr_fun h_lift F
  · simpa only [← hTp] using coordinateRow_edgeHeckeOperator_dvd T J 𝓔 h h_deep x₀ h₀ F

/-- One explicit adjacent Frobenius pairing supplies a primitive depth-one row
for the actual normalized scaled Hecke operator on the integral source lattice. -/
theorem exists_primitive_row_scaledHeckeOperator_of_adjacentPair
    {P : Parameters} {p : ℕ} {D : Data P} [Fact p.Prime] [PadicPlace p]
    {Λ : Finset (FinPlace D.E)} {l : FinPlace D.E} {N : ℕ}
    {W : ValuationSubring D.E} {θ : ℝ} {Q : D.Φ → Prop} [NeZero N]
    (hΛ : D.IsMarked Λ) (hlΛ : l ∈ Λ)
    (hW : W = (l.valuation D.E).valuationSubring) (T : FrobeniusCycle N W embValRing)
    (hTp : T.p = p) (t : ZMod N ≃ Subtype Q)
    (hQ : ∀ σ : D.Φ, Q σ ↔ σ ∈ D.aPlaces ∧
      (inducedPlace σ = l ∨ inducedPlace σ = star l))
    (hι : ∀ (i : ZMod N) (x : W),
      T.embedding i x = (if T.isEven i then Φ (t i).val else (Φ (t i)).comp conj) x)
    (h_exponent : heckeScalingExponent l = D.a * #{i : ZMod N | T.isEven i})
    (h_size : T.IsLargeDegree D.k D.a (D.ceilLogLifts p) θ)
    (s : ZMod N) (b₀ : Fin D.k) :
    ∃ (rowM : D.integralSourceForms →ₗ[embValRing] embValRing)
      (φ₀ : D.integralSourceForms), rowM φ₀ = 1 ∧
      ∀ φ : D.integralSourceForms,
        ∃ h_int : hΛ.scaledHeckeOperator ⟨l, hlΛ⟩ φ.val ∈ D.integralSourceForms,
          (p : embValRing) ∣ rowM ⟨hΛ.scaledHeckeOperator ⟨l, hlΛ⟩ φ.val, h_int⟩ := by
  have hp : ¬IsUnit (T.p : embValRing) := by
    simpa only [hTp] using (Data.not_isUnit_natCast_embValRing (p := p))
  have ha : T.P ≤ D.a := frobeniusPower_le_of_isLargeDegree T h_size
  exact exists_primitive_row_scaledHeckeOperator_of_deep_coefficients
    hΛ hlΛ hW T hTp t hQ hι h_exponent h_size (T.adjacentPairingRow D.a ha s b₀)
    (fun g β ↦ T.adjacentPairingRow_deep_dvd hp (D.ceilLogLifts p) D.a ha s b₀ g β)
    (T.pairingTermExponent D.a ha s b₀ b₀) (T.adjacentPairingRow_unit D.a ha s b₀)

end New.FrobeniusRowResearch

end
