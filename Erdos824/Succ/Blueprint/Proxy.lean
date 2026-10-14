import Erdos821.Blueprint.Proxy

/-!
# P8 for the successor sign

Only the second clause of `ProxyDensities` mentions the sign: `mn = 2u + 1` becomes
`mn + 1 = 2u`. The discrepancy, density identities and sieve products are
those of the Erdős 821 formalization (totient-fibers-lean4).
-/

noncomputable section
open scoped BigOperators
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace Erdos824.Succ
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- `Erdos821.Blueprint.ProxyDensities` with `m * n + 1 = 2 * u` in the rough clause. -/
def ProxyDensities : Prop :=
  (∃ K : ℝ, 0 < K ∧ ∀ kappa S : ℝ, 0 < kappa → kappa < 1 / 50 → 0 < S →
    ∀ᶠ x : ℝ in atTop, ∀ m : ℕ,
      x ^ (1 / 2 - 2 * kappa) ≤ (m : ℝ) → (m : ℝ) ≤ x ^ (1 / 2 + 2 * kappa) →
      proxyConstant .prime x S m ≤ K / (L x * sieveProduct (W x))) ∧
  (∀ b kappa S gamma gamma' eps : ℝ, 0 < b → 0 < kappa → kappa < 1 / 50 →
    0 < S → b ≤ gamma → gamma < gamma' → gamma' ≤ 1 / 2 - kappa → 0 < eps →
    ∀ᶠ x : ℝ in atTop, ∀ m n u : ℕ,
      m * n + 1 = 2 * u → x ≤ (u : ℝ) → (u : ℝ) ≤ 2 * x →
      gamma < Real.log n / L x → Real.log n / L x ≤ gamma' →
      proxyConstant (.rough gamma) x S m ≤
        (sSup ((fun a : ℝ => roughDensity gamma (1 - a)) '' Set.Icc gamma gamma') + eps) /
          (L x * sieveProduct (W x)))

structure ProxyInputs : Prop where
  discrepancy : ProxyDiscrepancy
  densities : ProxyDensities
  identities : DensityIdentities
  products : SieveProducts

abbrev proxy_inputs_statement : Prop :=
  ∀ (_hc : ClassicalInputs) (_hs : SieveInputs),
    ProxyInputs
end Erdos824.Succ
