-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/ThreeAtW.lean: no soundness is claimed.
Three of the clauses that the last chain's ledger asks of a member of the proximity test at the place W (Johnson/LLT25R/LastMembers.lean: FiveAt: hseed · hsmp · h2), from the sendings' invariant K1.SeedIs at the ends of the two earlier chains.
  ThreeOf cs sh e0 v t D j   the three clauses together, at a member j of the test's plain data, a shape sh, a radius e0 and the value v that the ledger's reader gives:
      hseed : ∃ ρ yv, K1.SeedIs cs sh t.st (D.mems.get j).id ρ yv
      hsmp  : v = K1.smpAt cs sh e0 t.st (D.mems.get j).id
      h2    : ∃ o, D.st.oracles[(D.mems.get j).id]? = some o ∧ ok (sampleL cs (D.mems.get j) o) = true
  OneTable cs sh   the five tests on the plan's shape that the read-back law asks (sampleL_of_seed, Johnson/Desc/K12/Law/SampleOfSeed.lean, through two_at_member, Johnson/Desc/Sound/SeedTwo.lean): rows of one kind alone
  SampleAt cs sh St o · sampleAtB · sampleAt_iff   a test with code on a statement: message number o is there, has the shape sh, and K12's files' test sampleL accepts it (at every seat with that shape and number: sampleL reads no more of a seat: sampleL_only)
  **three_elder**  a member whose number is an elder message's (the index masks' · W): from SampleAt at what the first chain hands on (f.st) and «the reader reads smpAt there»: at every shape: no read-back law is spent (at_record, Johnson/Desc/Sound/SeedAtRecord.lean)
  **three_copy**   the member that is Omega's copy: from SeedIs at the shared chain's end at Omega's number there and «the reader reads smpAt there»: the copy's rows are the shared chain's, renamed (SeedCarried.lean: seedIs_copy · smpAt_of_seeds)
Both under: the book-keeping at border 2 (shapeAt … 2 f o s = true) · the seat's door's accept (enterOwn s = .ok t) · Fixes · K1.Tie cs sh. three_elder: p.codes = cs. three_copy: OneTable cs sh.
Why the two part. By an evaluation at the real shapes (both sizes): OneTable is false at W's shape at the full size (1 main row and 1 mask row); it is true at the index masks' and at Omega's at both sizes, and at W's at the small size. So the read-back law cannot pay h2 at W. An elder message stands in the last chain's statement as it stands in the first chain's: the test's accept goes along with no law on a row. Omega's copy has renamed rows: there the invariant is carried (seedIs_copy) and read back, at a shape with one kind of rows.
Left, by name. At the ends: SampleAt at the two elder members (a Bool on the first chain's last state) · SeedIs at Omega in the shared chain's end (or SampleAt there: seedIs_of_sampleAt): facts along the fold: to be taken from «reached». Of make: the two conditions on the ledger's readers. On the plan: Tie at the three shapes · OneTable at Omega's.
Does not show. That either end holds the invariant. No member. Nothing on soundness.
-/
import Johnson.ToldDescR.RcLastCode
import Johnson.ToldDescR.SeedCarried
import Johnson.ToldDescR.OpensAtW
import Johnson.Desc.Sound.SeedTwo
import Johnson.Desc.Sound.SeedAtRecord
import Johnson.Desc.Third.Law.Start

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open OnBytes OnBytes.Params OnBytes.Slice Johnson.Pack Cb Cb.Ood
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin (Fixes)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut Border Laid)
open VerifiableInference.Desc.Third.Law (start₃E_border start₃E_st start₃E_inv start₃_inv)
open VerifiableInference.Desc.Last (Handed shapeAt BehindOk behindOk_of_two)
open H2K.First (Seat1 Plain ok)
open H2K.Pin (sampleL mainB maskB)

/-- **The three clauses.** v: what the ledger's reader gives at the member. -/
structure ThreeOf (cs : Codes) (sh : OracleShape) (e0 : ℕ) (v : Option (portOmZ cs sh e0).Smp)
    (t : T12) (D : Plain) (j : Fin D.mems.length) : Prop where
  hseed : ∃ ρ yv, K1.SeedIs cs sh t.st (D.mems.get j).id ρ yv
  hsmp : v = K1.smpAt cs sh e0 t.st (D.mems.get j).id
  h2 : ∃ o, D.st.oracles[(D.mems.get j).id]? = some o ∧
    ok (sampleL cs (D.mems.get j) o) = true

/-- The five tests on the plan's shape that the read-back law asks. -/
structure OneTable (cs : Codes) (s : OracleShape) : Prop where
  one : ¬ (0 < s.mainRows ∧ 0 < s.maskRows)
  some : 0 < s.mainRows ∨ 0 < s.maskRows
  case : (0 < s.maskRows ∨ s.mainDeg = 3) ∨ (s.maskRows = 0 ∧ s.mainDeg = 1)
  powM : s.mainRows = 0 ∨ 2 ^ ceilLog2 (mainB cs s).ell = (mainB cs s).ell
  powZ : s.maskRows = 0 ∨ 2 ^ ceilLog2 (maskB cs s).ell = (maskB cs s).ell

/-- The test `sampleL` reads of a seat its shape and its number alone. -/
theorem sampleL_only (K : Codes) {m m' : Seat1} (x : OnBytes.Oracle) (h1 : m'.sh = m.sh)
    (h2 : m'.id = m.id) : sampleL K m' x = sampleL K m x := by
  simp only [sampleL, h1, h2]

/-- **A statement holds message number o with the shape sh, and the test `sampleL` accepts it.** -/
def SampleAt (cs : Codes) (sh : OracleShape) (St : Statement) (o : ℕ) : Prop :=
  ∃ x, St.oracles[o]? = some x ∧ x.shape = sh ∧
    ∀ m : Seat1, m.sh = sh → m.id = o → ok (sampleL cs m x) = true

/- `sampleAtB`, the same as a test with code, stands in RcLastCode.lean. -/

theorem sampleAt_iff (cs : Codes) (sh : OracleShape) (St : Statement) (o : ℕ) :
    sampleAtB cs sh St o = true ↔ SampleAt cs sh St o := by
  unfold sampleAtB SampleAt
  constructor
  · intro h
    split at h
    · rename_i x hx
      rw [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨x, hx, h.1, fun m h1 h2 => by
        rw [sampleL_only cs (m := ⟨o, sh, 0, 0, default, 0⟩) x h1 h2]
        exact h.2⟩
    · cases h
  · rintro ⟨x, hx, h1, h2⟩
    rw [hx]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, h2 _ rfl rfl⟩

/-- The test's accept gives the sendings' invariant. -/
theorem seedIs_of_sampleAt {cs : Codes} {sh : OracleShape} {St : Statement} {o : ℕ}
    (h : SampleAt cs sh St o) (hc : St.codes = cs) (hT : K1.Tie cs sh) :
    ∃ ρ yv, K1.SeedIs cs sh St o ρ yv := by
  obtain ⟨x, hx, hs, hq⟩ := h
  exact _root_.Desc.K14.Law.Fence.seedIs_of_sampleL (m := ⟨o, sh, 0, 0, default, 0⟩) (hq _ rfl rfl)
    hx hs hc hT

/-- From the invariant at the test's own state, at ONE OOD seed and answer with the place where the
reader reads. -/
theorem three_of_seed {cs : Codes} {sh : OracleShape} {e0 : ℕ} {v : Option (portOmZ cs sh e0).Smp}
    {π : P12} {t : T12} {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : Group}
    {Ly : GroupLayout} {D : Plain} (hf : Fixes π t a rest G0 Ly D) (j : Fin D.mems.length)
    (hT : K1.Tie cs sh) (h1 : OneTable cs sh) {ρ : (Fin (bitsZ cs sh) → GE) × GEˣ} {yv : GE}
    (h : K1.SeedIs cs sh t.st (D.mems.get j).id ρ yv) {St₀ : Statement} {o₀ : ℕ}
    (h0 : K1.SeedIs cs sh St₀ o₀ ρ yv) (hv : v = K1.smpAt cs sh e0 St₀ o₀) :
    ThreeOf cs sh e0 v t D j :=
  ⟨⟨ρ, yv, h⟩, hv.trans (smpAt_of_seeds e0 hT h0 h),
    _root_.Desc.K14.Law.Fence.two_at_member hf default j hT h h1.one h1.some h1.case h1.powM
      h1.powZ⟩

section
variable {cs : Codes} {sh : OracleShape} {e0 : ℕ} {v : Option (portOmZ cs sh e0).Smp}
  {π : P12} {t : T12} {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : Group}
  {Ly : GroupLayout} {D : Plain} {p : P₁₄} {R : List Fmt.DeclaredRound} {f : Handed} {o : SharedOut}
  {s : S₃}

/-- **A member whose number is an elder message's**: at every shape. -/
theorem three_elder (hs : shapeAt p R 2 f o s = true) (he : enterOwn s = .ok t)
    (hf : Fixes π t a rest G0 Ly D) (j : Fin D.mems.length) (hT : K1.Tie cs sh)
    (hcs : p.codes = cs) (hE : SampleAt cs sh f.st (D.mems.get j).id)
    (hv : v = K1.smpAt cs sh e0 f.st (D.mems.get j).id) : ThreeOf cs sh e0 v t D j := by
  obtain ⟨⟨s₀, B⟩, -⟩ := behindOk_of_two hs
  obtain ⟨b, y, G, dot, L⟩ := B.laid
  have hst : s₀.st = f.st := start₃E_st _ _ _ _ _ _ _ _ _ _ _ B.start
  have et : t.st = s.st := by rw [enterOwn_is he]
  obtain ⟨x, hx, hsh, hq⟩ := hE
  have hi : (D.mems.get j).id < s₀.st.oracles.size := by
    rw [hst]
    exact (Array.getElem?_eq_some_iff.1 hx).1
  have hget : s.st.oracles[(D.mems.get j).id]? = f.st.oracles[(D.mems.get j).id]? := by
    rw [L.old _ hi, hst]
  have hc : s.st.codes = cs := by
    obtain ⟨f', _, hst'⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ B.start
    obtain ⟨c1, -, e⟩ := start₃_inv _ _ _ _ hst'
    rw [L.codes, e]
    exact c1.trans hcs
  obtain ⟨k1, k2⟩ := _root_.Desc.K14.Law.Fence.at_record (St₀ := s.st) et hc
    ⟨x, hget.trans hx, hsh, hq⟩ hT hf default j rfl
  refine ⟨k1, hv.trans (smpAt_congr cs sh e0 ?_ ?_), k2⟩
  · unfold K1.formsAt
    rw [et, hget]
  · unfold K1.ansAt
    rw [et, hget]

/-- **The member that is Omega's copy.** -/
theorem three_copy (hs : shapeAt p R 2 f o s = true) (he : enterOwn s = .ok t)
    (hf : Fixes π t a rest G0 Ly D) (j : Fin D.mems.length) (hT : K1.Tie cs sh)
    (h1 : OneTable cs sh) (hj : (D.mems.get j).id = s.loc.omega)
    (hE : ∃ ρ yv, K1.SeedIs cs sh o.st o.omega ρ yv)
    (hv : v = K1.smpAt cs sh e0 o.st o.omega) : ThreeOf cs sh e0 v t D j := by
  obtain ⟨⟨s₀, B⟩, -⟩ := behindOk_of_two hs
  obtain ⟨b, y, G, dot, L⟩ := B.laid
  obtain ⟨ρ, yv, h0⟩ := hE
  obtain ⟨g, hg⟩ := start₃E_border _ _ _ _ _ _ _ _ _ _ _ B.start
  obtain rfl : (⟨g, o⟩ : Border) = b := Option.some.inj (hg.symm.trans L.border)
  have et : t.st = s.st := by rw [enterOwn_is he]
  have hc : s₀.st.codes = cs := by
    obtain ⟨f', _, hst'⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ B.start
    obtain ⟨c1, c2, e⟩ := start₃_inv _ _ _ _ hst'
    rw [e]
    exact c1.trans (c2.symm.trans h0.1)
  have h : K1.SeedIs cs sh t.st (D.mems.get j).id ρ yv := by
    rw [et, hj, omega_is L]
    exact seedIs_copy L hc h0
  exact three_of_seed hf j hT h1 h h0 hv

end

end ToldDesc

#print axioms ToldDesc.sampleAt_iff
#print axioms ToldDesc.seedIs_of_sampleAt
#print axioms ToldDesc.three_of_seed
#print axioms ToldDesc.three_elder
#print axioms ToldDesc.three_copy
