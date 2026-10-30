-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/KeyFillStep.lean: ONE STATEMENT INSIDE On₁' 1 (THE FIRST CHAIN's PROMISE BEHIND ITS FIRST BLOCK, WITH ITS HISTORY) FROM A YES OF THAT BLOCK's OWN STEP AT THE CHAIN's START. Johnson/RunOne/KeyFillOn.lean's on₁_of_tests leaves as L1 «the state holds the sending kind's row at every open pin», which is no Bool.
Here the record a IS THE VALUE OF THE FIRST BLOCK's STEP at the start: so the history Hist₁ 1 holds by definition, and L1 is a theorem: isSend10 (Row10At.lean) hands the sending's decision's yes, K1.seedIs_behind (Johnson/Desc/K1/Law/SeedIs.lean) the row, SeedIs.travels carries it to a.
  seed_cast        SeedIs along two equations of codes and shape, under ∃ ρ y
  l2_of_cell       the stored table's side is asked AT y₀ ALONE, where «collision» reads the cells alone (CollCell)
  hist₁_of_step    the step's yes at the start IS the history at border 1
  seedIs_of_step   the step's yes ⟹ ∃ ρ y, SeedIs (par10 X).codes (shapeAt (par10 X) k₀) a.2.d.st (size − length + k₀) ρ y
  on₁'_of_step     ∃ y', On₁' X N P D baseK atSix kreadFam coll 1 (a, y')
THE PREMISES OF on₁'_of_step: q₁ (the chain's first block is c₁) · THE STEP's YES at two rounds · T1-T4 of on₁_of_tests at a · Z1 the state's statement has one message · L2 the stored table's side · the six closed tests · PUBLIC: condPort (par10 X) rad = true · sampledAt (par10 X) k₀ · the sending has one shape
  · TWO TIES: (par10 X).codes = csKey · shapeAt (par10 X) k₀ = shIdx. THAT THE DRAWN FACTOR READS AS NO 0 IS NO PREMISE: Johnson/Top/Fire/Code/KeyFillFactor.lean: out of the same yes (the held block's words' test and the sending's own test), by K1.reads_exists.
THAT SUCH ROUNDS AND COLUMNS EXIST IS NOT SHOWN (a stored honest view: an evaluation's); THE ORACLES y' ARE BUILT BY THE PROOF. UNTIL ALL PREMISES ARE SEEN TOGETHER AT ONE VIEW THIS MAY BE TRUE AND EMPTY.
OBJECT: On₁' | Hist₁ | Reached; isSend10; K1.seedIs_behind · USER: KeyFillYes.lean (on₁'_of_step) · LETTERS: X N P D · x · r₁ r₂ cols · decT recOf tab coll rad.
Nothing on soundness.
-/
import Johnson.RunOne.KeyFillOn
import Johnson.Top.Fire.Code.KeyTablesR
import Johnson.Top.Fire.Code.Row10At
import Johnson.RunOne.KeySendYes
import Johnson.Top.Fire.Code.KeyFillFactor
import Johnson.Desc.K1.Law.Sound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

namespace LPFD
open OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi FirstState)
open VerifiableInference.Desc.Key.Fill (six)
open Johnson.RunOne.KeyRows23 (Fk fr₁ On₁ oneAt baseK kreadFam numSix atSix holdsB on₁_of_tests)
open Johnson.RunOne.KeyRows1 (plan₁ readers₁ book₁ n₁ slots₁ open₁)
open VerifiableInference.Desc.K1 (Par condPort IsSend SeedIs ReadsAs Seeds seedsOf shapeAt shapesOf sampledAt seedIs_behind seedAt)
open Johnson.Pack (aOf bitsZ)

theorem seed_cast (cs cs' : OnBytes.Codes) (s s' : OnBytes.OracleShape) (St : OnBytes.Statement) (o : ℕ) (hc : cs = cs') (hs : s = s') (h : ∃ ρ y, SeedIs cs s St o ρ y) :
    ∃ ρ y, SeedIs cs' s' St o ρ y := by
  subst hc hs
  exact h

/-- Where «collision» reads of the oracles the stored table's cells alone (CollCell), no collision at y₀ is no collision at every y' with y₀'s stored side. -/
theorem l2_of_cell {Rec : Type} (Fr : Frame) (coll : Strs → Rec → Prop) (hc : Johnson.RunOne.KeyRows1.CollCell coll) (y₀ : Fr.E.Str) (r : Rec) (h : ¬ coll (strsOf Fr y₀) r) :
    ∀ y' : Fr.E.Str, y'.1 = y₀.1 → ¬ coll (strsOf Fr y') r := fun y' hy hcl =>
  h (hc (strsOf Fr y₀) (strsOf Fr y') r (by
    show cellAt Fr y' = cellAt Fr y₀
    funext x
    unfold cellAt
    rw [hy]) hcl)

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (D : WholeD)
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))

/-- **The step's yes at the start is the history at border 1.** -/
theorem hist₁_of_step (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (x : (Fk X N P).XiPub) (rs : List _root_.Fmt.RoundView) (cols : List OpenedColumn) (a : (Fk X N P).XiPub × (Fk X N P).S₁) (n : ℕ)
    (hstep : (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl).step (fr₁ D).ft (x, (Fk X N P).start₁ x) rs cols = .ok (a, n)) : Hist₁ (Fk X N P) D 1 a :=
  ⟨(x, (Fk X N P).start₁ x), held c₁, rs, cols, n, rfl, by rw [q₁]; rfl, hstep⟩

/-- **The step's yes gives the sending kind's row in the record.** -/
theorem seedIs_of_step (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (rad : ℕ → ℕ) (hC : condPort (par10 X) rad = true) (ft : ℕ) (a₀ a : Xi × FirstState) (r₁ r₂ : _root_.Fmt.RoundView) (cols : List OpenedColumn) (n : ℕ)
    (hstep : (held c₁ : Block (Xi × FirstState) Claim).step ft a₀ [r₁, r₂] cols = .ok (a, n))
    (k₀ : Fin (shapesOf (par10 X)).length) (hk : sampledAt (par10 X) k₀) :
    ∃ ρ y, SeedIs (par10 X).codes (shapeAt (par10 X) k₀) a.2.d.st (a.2.d.st.oracles.size - (shapesOf (par10 X)).length + k₀.val) ρ y := by
  have hd : (held c₁ : Block (Xi × FirstState) Claim).decide a₀ [noDigest r₁, noDigest r₂] _ = .ok a := step_decides hstep
  have hf : roundsFit (held c₁ : Block (Xi × FirstState) Claim).rounds [r₁, r₂] = true := (step_fits hstep).1
  obtain ⟨L, d, d', owed, ids, hyes, hsame, hsz⟩ := isSend10 X N P c₁ k₁ q₁ _ _ _ _ _ hd
  have hok := drawn_ok _ (held_okView c₁ _ _ _ _ hd) (noDigest r₁) List.mem_cons_self
  obtain ⟨ρ, hρ⟩ := VerifiableInference.Desc.K1.reads_exists (par10 X) (noDigest r₁) (factor_ok (par10 X) _ hok) ((VerifiableInference.Desc.K1.decideSend_iff (par10 X) owed d d' _ _ ids).1 hyes).1.2.2.1
  have hf' : roundsFit (K1.rounds (par10 X)) [noDigest r₁, noDigest r₂] = true := by
    have e : (held c₁ : Block (Xi × FirstState) Claim).rounds = K1.rounds (par10 X) := by
      show c₁.rounds = _
      rw [first_is X N P c₁ k₁ q₁]
      exact List.append_nil _
    rw [e] at hf
    exact (Johnson.RunOne.KeyRows1.roundsFit_noDigest' _ [r₁, r₂]).trans hf
  obtain ⟨y, hy⟩ := seedIs_behind (par10 X) rad owed d d' _ _ ids hC hf' hyes ρ hρ k₀ hk
  have hsize := VerifiableInference.Desc.K1.size_behind (par10 X) owed d d' _ _ ids hyes
  have e2 : a.2.d.st.oracles.size - (shapesOf (par10 X)).length + k₀.val = d.st.oracles.size + k₀.val := by
    rw [hsz, hsize]
    omega
  rw [e2]
  exact ⟨_, y, hy.travels hsame⟩

end

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (D : WholeD)
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
    {Cells Rec : Type} [Inhabited Cells] (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec) (tab : Cells → ℕ → ℕ → OnBytes.F) (coll : Strs → Rec → Prop)

/-- **ONE STATEMENT INSIDE On₁' 1, FROM A YES OF THE FIRST BLOCK's OWN STEP AT THE START.** -/
theorem on₁'_of_step (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (rad : ℕ → ℕ) (hC : condPort (par10 X) rad = true)
    (x : Xi) (a : Xi × FirstState) (r₁ r₂ : _root_.Fmt.RoundView) (cols : List OpenedColumn) (n : ℕ)
    (hstep : (held c₁ : Block (Xi × FirstState) Claim).step (fr₁ D).ft (x, (Fk X N P).start₁ x) [r₁, r₂] cols = .ok (a, n))
    (k₀ : Fin (shapesOf (par10 X)).length) (hk : sampledAt (par10 X) k₀) (Z2 : (shapesOf (par10 X)).length = 1)
    (tieC : (par10 X).codes = Johnson.Top.H.csKey) (tieS : shapeAt (par10 X) k₀ = Johnson.Top.H.shIdx)
    (Z1 : a.2.d.st.oracles.size = 1)
    (t0 t1 t2 : String)
    (n0 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t0 Johnson.Top.H.shIdx 0 0 = none)
    (n1 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t1 Johnson.Top.H.shMul 1 0 = none)
    (n2 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t2 Johnson.Top.H.shW 5 0 = none)
    (f0 : holdsB (fr₁ D) 0 (aOf Johnson.Top.H.csKey Johnson.Top.H.shIdx) = true)
    (f1 : holdsB (fr₁ D) 1 (aOf Johnson.Top.H.csKey Johnson.Top.H.shMul) = true)
    (f2 : holdsB (fr₁ D) 5 (aOf Johnson.Top.H.csKey Johnson.Top.H.shW) = true)
    (y₀ : (fr₁ D).E.Str)
    (T1 : shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁ (oneAt X)) 1 a.2 = true)
    (T2 : Placed (plan₁ (oneAt X)).orc (fun o => a.2.d.book.place[o]?) id atSix (pinned (open₁ 2 1)))
    (T3 : OnBytes.Means.InOrder a.2.d.st)
    (T4 : a.1.key.fits (oneAt X).lin.fold.index = true)
    (r : Rec) (L2 : recOf a.1 = some r) (hcell : Johnson.RunOne.KeyRows1.CollCell coll) (L2' : ¬ coll (strsOf (fr₁ D) y₀) r) :
    ∃ y' : (fr₁ D).E.Str, y'.1 = y₀.1 ∧
      On₁' X N P D (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (plan₁ (oneAt X)).orc) atSix (kreadFam Johnson.Top.H.csKey six numSix atSix tab) coll 1 (a, y') := by
  have hS := seedIs_of_step X N P c₁ k₁ q₁ rad hC (fr₁ D).ft _ a r₁ r₂ cols n hstep k₀ hk
  have hidx : a.2.d.st.oracles.size - (shapesOf (par10 X)).length + k₀.val = 0 := by
    have := k₀.isLt
    omega
  rw [hidx] at hS
  have hS' := seed_cast _ _ _ _ _ _ tieC tieS hS
  have hpin : ∀ q ∈ pinned (open₁ 2 1), q = 0 := by decide +kernel
  obtain ⟨y', hy, hon⟩ := on₁_of_tests X N P D decT recOf tab coll 1 (by decide) t0 t1 t2 n0 n1 n2 f0 f1 f2 y₀ a T1 T2 T3 T4 (fun h => absurd h.1 (by decide))
    (fun i hi => by
      obtain ⟨q, hq⟩ := i
      have h0 : q = 0 := hpin q hi
      subst h0
      obtain ⟨ρ, y, h⟩ := hS'
      exact ⟨0, ρ, y, rfl, h⟩) r L2 (l2_of_cell (fr₁ D) coll hcell y₀ r L2')
  exact ⟨y', hy, hon, hist₁_of_step X N P D c₁ k₁ q₁ x _ cols a n hstep⟩

end

end LPFD

#print axioms LPFD.seed_cast
#print axioms LPFD.l2_of_cell
#print axioms LPFD.hist₁_of_step
#print axioms LPFD.seedIs_of_step
#print axioms LPFD.on₁'_of_step
