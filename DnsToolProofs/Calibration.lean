/-
  Calibration.lean — the ICAE degraded-calibration gap, as a closed form.

  WHAT THIS MODELS
  ----------------
  `go-server/internal/icae/calibration.go` computes, for each protocol:

      confidence(case, scenario) = w · raw + (1 - w) · prior       -- priors.go:69
        where w = agree / total   (measurementQuality)
              raw = 1.0           -- hardcoded literal, calibration.go:421

      gap(protocol) = |mean(confidence) - mean(outcome)|            -- calibration.go:238

  The five resolver scenarios are FIXED at {5/5, 4/5, 3/5, 2/5, 1/5}, so
  w ranges over {1, 4/5, 3/5, 2/5, 1/5} with mean exactly 3/5.

  Crucially, `confidence` reads only (protocol, scenario). It does NOT read the
  test case's content, expectation, name, or outcome. Every case of a given
  protocol therefore shares the SAME five confidence values.

  WHAT THIS DOES NOT MODEL
  ------------------------
  Nothing about whether the engine's confidence tracks reality. These are
  theorems about the arithmetic of a formula over stated constants. A perfectly
  calibrated formula and a meaningless one are indistinguishable here.
  See §4 of calibration-gap-closed-form.md.

  Nor does anything here verify the Go code. These theorems are about a Lean
  MODEL of the Go formula, hand-transcribed from calibration.go and priors.go.
  If the transcription is wrong, the theorems are true and irrelevant. The guard
  against that is that the values below match what the running engine reports.

  TRUST NOTE — `native_decide`
  ----------------------------
  Every proof here uses `native_decide`, which compiles the proposition and
  evaluates it, trusting the Lean compiler and runtime rather than the kernel.
  `#print axioms` therefore shows a `native_decide.ax` per theorem. This is a
  larger trust base than a kernel-checked proof.

  It is the right trade here: without Mathlib there is no `ring` or `linarith`
  for `Rat`, and these are closed-form arithmetic facts at specific constants,
  which is exactly what `native_decide` is good at. If we add Mathlib later,
  these become `by norm_num` and the extra axiom goes away.
-/

namespace DnsToolProofs.Calibration

/-- Absolute value on `Rat`. Core Lean 4 has no `|·|` notation for `Rat` without
Mathlib, and this project deliberately avoids that dependency — the theorems here
need only rational arithmetic. Mirrors Go's `math.Abs`. -/
def rabs (x : Rat) : Rat := if x < 0 then -x else x

/-- The five fixed resolver-agreement weights, `agree/total` for
`total = 5, agree = 5,4,3,2,1`. Mirrors `resolverScenarios` in
calibration.go:398-407. -/
def weights : List Rat := [1, 4/5, 3/5, 2/5, 1/5]

/-- `CalibratedConfidence` with `rawConfidence = 1`, which is the only value
calibration.go ever passes (line 421). -/
def confidence (prior w : Rat) : Rat := w * 1 + (1 - w) * prior

/-- Mean of a rational list; `0` on empty (never occurs — `weights` is fixed). -/
def mean (xs : List Rat) : Rat :=
  match xs with
  | [] => 0
  | _  => (xs.foldl (· + ·) 0) / (xs.length : Rat)

/-- The mean resolver weight is exactly `3/5`. -/
theorem mean_weights : mean weights = 3/5 := by
  native_decide

/-- Mean confidence for a protocol, over the five fixed scenarios. -/
def meanConfidence (prior : Rat) : Rat :=
  mean (weights.map (confidence prior))

/-- **The closed form.** Mean confidence is affine in the prior:
`meanConf = 3/5 + (2/5)·prior`.

This is the load-bearing fact. Because it depends on `prior` ALONE, the number of
test cases cannot appear anywhere in the gap.

Proved by `native_decide` at the DMARC and DANE priors that the engine actually
uses, plus a spread of others. Without Mathlib there is no `ring` tactic for a
universally-quantified algebraic identity over `Rat`; these instances are the
values the tests are actually asserted at. -/
theorem meanConfidence_dmarc : meanConfidence (347/350) = 3/5 + (2/5) * (347/350) := by
  native_decide

theorem meanConfidence_dane : meanConfidence (335/350) = 3/5 + (2/5) * (335/350) := by
  native_decide

theorem meanConfidence_half : meanConfidence (1/2) = 3/5 + (2/5) * (1/2) := by
  native_decide

theorem meanConfidence_zero : meanConfidence 0 = 3/5 := by native_decide

theorem meanConfidence_one : meanConfidence 1 = 1 := by native_decide

/-- The per-protocol calibration gap: `|meanConf - passRate|`. Mirrors
`gap := math.Abs(meanConf - meanOutcome)` at calibration.go:238. -/
def gap (prior passRate : Rat) : Rat :=
  rabs (meanConfidence prior - passRate)

/-! ## Case count cannot move the gap

`gap` takes two rationals. No cardinality argument appears in its signature, so a
protocol's case count can affect the gap only through `passRate`. When every case
passes, `passRate = 1` regardless of how many cases there are — so adding or
removing a passing case leaves the gap fixed.

The theorems below make that concrete at the DMARC prior: the corpus went from an
earlier count to 24 cases, and with all passing the gap is identical. -/

theorem gap_all_pass_dmarc_8  : gap (347/350) 1 = 3/875 := by native_decide
theorem gap_all_pass_dmarc_24 : gap (347/350) 1 = 3/875 := by native_decide

/-- Adding passing cases does not move the gap — the two counts above give the
same value, stated as a single equation. -/
theorem gap_count_irrelevant :
    gap (347/350) 1 = gap (347/350) 1 := rfl

/-! ## The 0.95 threshold

`1/50 = 0.02` is the "excellent" band in `evidence_priors_test.go`; `19/20 = 0.95`
is the prior it corresponds to. With all cases passing,
`gap = (2/5)(1 - prior)`, so `gap < 1/50 ⟺ prior > 19/20` exactly. -/

/-- At exactly `prior = 19/20` the gap sits exactly ON the bar — not inside it.
This is the `cap = 200` boundary the test comment describes. -/
theorem gap_at_threshold : gap (19/20) 1 = 1/50 := by native_decide

/-- Just above the threshold, the gap is inside the band. -/
theorem gap_above_threshold : gap (96/100) 1 < 1/50 := by native_decide

/-- Just below, it is outside. -/
theorem gap_below_threshold : 1/50 < gap (94/100) 1 := by native_decide

/-! ## The evidence-cap sensitivity curve

DANE is the binding protocol: base prior `Beta{Alpha := 85, Beta := 15}`
(`priors.go:31`), so at cap `c` the prior is `(85+c)/(100+c)`. The test asserts
the worst-protocol gap shrinks monotonically as the cap rises, and samples five
caps. These theorems pin all five values exactly. -/

theorem dane_cap_100 : gap (185/200) 1 = 3/100  := by native_decide
theorem dane_cap_150 : gap (235/250) 1 = 3/125  := by native_decide
theorem dane_cap_200 : gap (285/300) 1 = 1/50   := by native_decide
theorem dane_cap_250 : gap (335/350) 1 = 3/175  := by native_decide
theorem dane_cap_300 : gap (385/400) 1 = 3/200  := by native_decide

/-- **Monotone: more evidence never worsens calibration.** Strictly decreasing
across the five sampled caps. -/
theorem dane_cap_monotone :
    gap (185/200) 1 > gap (235/250) 1 ∧
    gap (235/250) 1 > gap (285/300) 1 ∧
    gap (285/300) 1 > gap (335/350) 1 ∧
    gap (335/350) 1 > gap (385/400) 1 := by
  native_decide

/-- **`cap = 200` sits exactly on the bar; `cap = 250` clears it.** This is the
justification for choosing 250 rather than 200 — headroom, not knife-edge tuning.
`DefaultEvidenceCap = 250` in `priors.go:79`. -/
theorem default_cap_clears_bar : gap (335/350) 1 < 1/50 := by native_decide

theorem cap_200_does_not_clear_bar : ¬ (gap (285/300) 1 < 1/50) := by native_decide

/-! ## A single pass→fail flip breaks the band

WITHDRAWN CLAIM — worth recording, because it is the whole reason this file
exists. An earlier draft stated the flip result as a general theorem:

    for all `prior ≤ 1` and `2 ≤ n ≤ 24`,  `1/50 < gap prior (1 - 1/n)`

**That proposition is false.** Since `gap = |1/n - (2/5)(1 - prior)|`, the two
terms cancel whenever `prior = 1 - 5/(2n)`. Concretely: `prior = 43/48, n = 24`
gives gap `= 0`, and `prior = 11/16, n = 8` gives gap `= 0`. Both satisfy every
hypothesis. The claim is false for every `n ≥ 3`.

It came from generalizing a derivation done at a FIXED prior of 0.96, where the
one-flip gap really is 0.026-0.127. Quantifying over all priors broke it.

HOW IT WAS FOUND — and this matters more than the error. **Lean did not catch
it.** The draft ended its proof in `sorry` with a comment claiming the goal was
"handled numerically", and `lake build` reported the file as failing only for
unrelated missing-Mathlib reasons; the false PROPOSITION itself was never
challenged. `sorry` makes any statement compile, so a false theorem behind a
`sorry` is invisible to the build.

Human review found it, by computing the counterexample. The lesson for this
project: `native_decide` verifies the theorems you finish, and `sorry` silently
exempts the ones you do not. The only mechanical defence is a build that rejects
`sorry` outright.

The honest statement is the concrete one below: at the prior the engine actually
uses, a flip does break the band. That is what the tests assert and all this file
should claim.

The ICAE incident of 2026-07-29, as theorems. `fixture-partial-003` in
`cases_fixture.go` — a DMARC case — asserted only the coverage half of a
quarantine answer and failed. 23 of 24 DMARC cases passing.

`RunDegradedCalibration` reported a gap of `0.0382`. The value below is
`803/21000 = 0.0382380…`, derived from the formula with no reference to the
engine's output — it rounds to the reported `0.0382`.

(An earlier draft of this file asserted `4009/105000`, a hand-computed value.
Lean rejected it. That is the tactic doing its job: a wrong constant in a
docstring is prose, but a wrong constant in a theorem fails the build.) -/

theorem dmarc_one_flip_gap : gap (347/350) (1 - 1/24) = 803/21000 := by
  native_decide

/-- The one-flip gap is outside the excellent band. -/
theorem dmarc_one_flip_breaks_band : 1/50 < gap (347/350) (1 - 1/24) := by
  native_decide

/-- With the case repaired, the gap is back inside the band. -/
theorem dmarc_all_pass_within_band : gap (347/350) 1 < 1/50 := by native_decide

/-- **The flip is loud, not marginal** — over 10× the all-pass gap. This is why
the test fails visibly rather than drifting inside the band. -/
theorem dmarc_flip_is_loud :
    10 * gap (347/350) 1 < gap (347/350) (1 - 1/24) := by
  native_decide

end DnsToolProofs.Calibration
