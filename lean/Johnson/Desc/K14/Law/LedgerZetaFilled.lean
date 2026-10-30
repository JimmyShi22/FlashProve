-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerZetaFilled.lean: "LIN zeta" AT THE LEDGER OF A PROOF FILE's SHARED CHAIN,
AT THE SHARED TABLE's FILLING OF THE PINS AND THE PROMISE (zeta_at_sig,
Johnson/Desc/K14/Law/LedgerZetaAt.lean) AND WITH THIS KIND's LETTERS FILLED as
Johnson/Desc/K14/Law/Filling.lean and ShapesSend.lean fill them: omU := OmU (Omega is, row by row of
M, what u gives at the point's low part) · row (fold) := FoldAt · shape 7, shape 8 := shapeO at the
same two counts of open rows. A JOINING.

  open7_other     a shared item that is open at border 7, is not named by row 7 and is no pin is a
                  class of rows other than (fold): by evaluation of the table.
  zeta_filled     **the clause at block 7.**
WHAT IS LEFT, AND WHOSE. By make: hz · hd · he. Numbers of the plan and the tiling: hB, hB'. The
plan's mem and its two members' seats. The table's letters read no z_fd: smp₂ (hsm), the stored
table's promise (htab). huR: where o_u is seated the table's
reader of the record is the record. htie: the tie of the table's reader omW of the witness's Omega
to the words: inside shape 7, omW w y is the word at the number noted for o_omega, at the layout's
index of y. hrowZ: a class of rows other than (fold) reads no z_fd (at slices of the groups' lists
as they lie: by unfolding). The four equations of letters: rfl where the letters are so filled.
What is not claimed. NO MEMBER: no letters and statement are shown at which all premises hold
together. A block that refuses all meets the clause. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.LedgerZetaAt
import Johnson.Desc.K14.Law.Filling

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block Strs Wit FileDescription smpHeld)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared

/-- A shared item that is open at border 7, is not named by row 7 and is no pin is a class of rows
other than (fold). -/
theorem open7_other (split : Bool) (i : ItemS) (ho : openSh split 7 i) (hi : ¬ insSh split 7 i)
    (hp : ∀ m, i ≠ .pin m) : ∃ c, i = .row c ∧ c ≠ .fold := by
  have h' := (openSh_iff split 7 i).1 ho
  have e : ∀ j ∈ openL (insLSh split) (outsLSh split) startLSh 7,
      j ∈ ([.omU, .pin .oU, .pin .oOmega, .pin .oSp, .row (.sample .oU), .row .recG, .row .loc,
        .row (.sample .oOmega), .row (.sample .oSp)] : List ItemS) := by
    cases split <;> decide
  have h2 := e i h'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
  rcases h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd ((ins7 split _).2 (Or.inl rfl)) hi
  · exact absurd rfl (hp _)
  · exact absurd rfl (hp _)
  · exact absurd rfl (hp _)
  · exact ⟨_, rfl, by decide⟩
  · exact ⟨_, rfl, by decide⟩
  · exact ⟨_, rfl, by decide⟩
  · exact ⟨_, rfl, by decide⟩
  · exact ⟨_, rfl, by decide⟩

variable {P₁ Cl Xi Cells Tok : Type} {Fr : Frame} (cs : OnBytes.Codes) (G : FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (c₀ : Cells)
  (stOf : St → OnBytes.Statement) (bookOf : St → OnBytes.TreeBook)
  (N : NumbersS) (Mg : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm : PromMeaning St)
  (Oc : P₁ → Strs → Prop) (split : Bool)
  (p : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))

/-- **"LIN zeta" at the ledger, the letters filled.** -/
theorem zeta_filled (P : Par) (mem : ℕ → Option Mem)
    (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE) (nU nO cU cO : ℕ)
    (xU xO : Mem) (hU : mem nU = some xU) (hO : mem nO = some xO) (mU : xU ∈ ms) (mO : xO ∈ ms)
    (sU : SitsAt xU (N.tenant .oU).1 (N.tenant .oU).2)
    (sO : SitsAt xO (N.tenant .oOmega).1 (N.tenant .oOmega).2)
    (uR : St → St) (omW : Wit Cells Tok MsgT → ℕ → GE)
    (b : Block (P₁ × St) Cl) (base : ℕ) (d : RDT)
    (ex : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT →
      Wit Cells Tok MsgT)
    (er : Err (uLT (ckP .two) [d])) {ns a0 : ℕ} (hd : SendsDraws (toRD d) ns P.S.kRow 0 a0)
    (e : ℕ) (he : P.S.kRow * Fintype.card GE ^ (P.S.kRow - 1) ≤ e)
    (hz : ∀ t rs gs t', b.decide t rs gs = .ok t' → linZeta t.2 rs = some t'.2)
    (hB : ∀ m, PromS.noColl m ∈ promsAt split 8 → SentBefore N p l 7
      (⟨b, base, [d], [], ex, er⟩ : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) m)
    (hB' : ∀ m, openSh split 7 (.pin m) → SentBefore N p l 7
      (⟨b, base, [d], [], ex, er⟩ : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) m)
    (hsm : ∀ (s : St) z, smp₂ { s with loc := { s.loc with zFd := z } } = smp₂ s)
    (htab : ∀ (s : St) z y y', y'.cell = y.cell → Pm.tablePromise s y →
      Pm.tablePromise { s with loc := { s.loc with zFd := z } } y')
    (huR : ∀ s, seatedUB P s = true → uR s = s)
    (htie : ∀ s w, shapeO P nU nO cU cO s = true → ∀ y < P.S.matrixRows,
      omW w y = omegaOf s.loc (linLayOmega s.st.codes P.S) (rgOf cs arr mem rd w) y)
    (hrowZ : ∀ c, c ≠ RowS.fold → ∀ (s : St) z w,
      Mg.row c { s with loc := { s.loc with zFd := z } } w → Mg.row c s w)
    (hoU : Mg.omU = OmU P uR (rgOf cs arr mem rd) omW)
    (hrF : Mg.row .fold = fun s w => FoldAt OnBytes.Model.Reading.gl P.S s (rgOf cs arr mem rd w))
    (hS7 : Pm.shape 7 = shapeO P nU nO cU cO) (hS8 : Pm.shape 8 = shapeO P nU nO cU cO) :
    ClauseAt N (meaningSigS cs G arr smp₂ ms decT₂ Mg) (promSigS cs G smp₂ ms stOf bookOf Pm) Oc
      split p l
      (fun k v w => extS cs G arr smp₂ ms decT₂ c₀ N split k v.1 (strsOfAct Fr v) w) 7
      (⟨b, base, [d], [], ex, er⟩ : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
      ((vecMaps d P.S.kRow).err ((e, ()) : ℕ × Unit)) := by
  have hsh : ∀ x, onQ₂ N (promSigS cs G smp₂ ms stOf bookOf Pm) Oc split p l 7 x →
      shapeO P nU nO cU cO x.1.2 = true := by
    intro x hx
    have h1 : Pm.shape 7 x.1.2 = true := hx.1 (.shape 7) (by simp [promsAt])
    rw [hS7] at h1
    exact h1
  refine zeta_at_sig cs G arr smp₂ ms decT₂ c₀ stOf bookOf N Mg Pm Oc split p l P.S mem rd nU nO xU
    xO hU hO mU mO sU sO b base d ex er hd e he hz hB hB' hsm ?_ ?_ ?_ ?_ htab ?_
  · intro x w hx h
    have hs := hsh x hx
    obtain ⟨hsU, _⟩ := (shapeO_iff P nU nO cU cO x.1.2).1 hs
    have hseat := ((shapeU_iff P nU cU x.1.2).1 hsU).2.1
    rw [hoU]
    intro y hy
    rw [htie x.1.2 w hs y hy, huR x.1.2 hseat]
    exact h y hy
  · intro y w _ h
    rw [hrF] at h
    exact h
  · intro x hx
    obtain ⟨hsU, _, eO, _⟩ := (shapeO_iff P nU nO cU cO x.1.2).1 (hsh x hx)
    exact ⟨((shapeU_iff P nU cU x.1.2).1 hsU).2.2.1, eO⟩
  · intro s z h
    rw [hS7] at h
    rw [hS8]
    exact h
  · intro x τ y w i _ hout ho hi hp hm
    obtain ⟨c, rfl, hc⟩ := open7_other split i ho hi hp
    obtain ⟨_, gs, hdd⟩ := piece_yes (⟨b, base, [d], [], ex, er⟩ :
      Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) x τ y hout
    have k7 := hz _ _ _ _ hdd
    obtain ⟨r7, hr⟩ := linZeta_one _ _ _ k7
    rw [hr] at k7
    have e7 := linZeta_inv x.1.2 y.1.2 r7 k7
    have hm' : Mg.row c y.1.2 w := hm
    rw [e7] at hm'
    exact hrowZ c hc x.1.2 _ w hm'

end Desc.K14.Law
