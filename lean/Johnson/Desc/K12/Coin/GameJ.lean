-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GameJ.lean: **THE GAME OF THE PROXIMITY TEST AT A SEAT, ITS PUBLIC PREMISES
THREE TESTS WITH CODE, ONE EQUATION AND ONE COMPARISON.** Definitions, statements and proofs, over
the block's parts with guard (c).

GameSeat.lean's law asks `AtPlace` | `AtPlaceOwn`, in which two fields are no tests: the facts on
codes (`CodesAt`) and "εt bears the chain's errors". Here the letters are the library's Johnson
letters at the radii r, and εt is the chain's own list of counts. Then both are paid:
`codes_of_johOk` (Johnson/Desc/K12/Law/CodesJoh.lean, the kind's own law's side: a yes of `johOk`
gives `CodesAt`, through the theorem on codes) and `bears_own` (BearsOwn.lean).

  `atPlace_joh` | `atPlaceOwn_joh`: `PlaceB` | `PlaceOwnB` (BoolsTests.lean), the stretch's
    numbering of the chain's own trees, `johOk`, and the place's chain c₀ with as many rounds as the
    stretch behind "BAT" give `AtPlace` | `AtPlaceOwn` at these letters and εt.
  `own_pays`: the stretch is like the written rounds, `johOk`, `batOneOk`: the second arm's three
    premises on "BAT"'s round, at v₀ := `batV0 π r`.
  `K12GameJ`, `k12_gameJ`; `K12GameJO`, `k12_gameJO`: the game at every seat from these.
  `chainFrom_rds`: the chain that `chainFrom` gives stands over just the written rounds handed to
    it.
  `errJ π r dt`: the chain's own counts as a function of the plan; `bears_errJ`: they bear the
    chain's errors wherever the stretch is like the written rounds.
  `K12GameT`, `k12_gameT`; `K12GameTO`, `k12_gameTO`: **the game at every seat at the errors
    (e, errJ π r dt)**: no letter for a chain is left.
What `K12GameT` | `K12GameTO` leave beside the promise `FirstOpens` | `FirstOpensOwn`: three tests
with code (`PlaceB` | `PlaceOwnB`, `johOk`, `batOneOk`); one equation on the numbering; e at least
the batching's count.
Limits: those of GameSeat.lean. NO SOUNDNESS IS CLAIMED. The tests' yes is a run's word; nothing has
been evaluated here. THAT THE COUNTS ARE SMALL against their rounds' numbers of challenges IS NOT
SAID: at counts that are not small the law is idle. The theorem on codes rests on the files under
ThirdParty/ (lean/LIMITS.md, L15). r is a letter: which radius a plan means is not said.

-/
import Johnson.Desc.K12.Coin.GameSeat
import Johnson.Desc.K12.Coin.BoolsOwn
import Johnson.Desc.K12.Coin.BearsOwn
import Johnson.Desc.K12.Law.CodesJoh

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Pin (NTuple)
open H2K.Pub (sgOf writtenOf WR chainFrom Letters kk PayPub johOk batV0 codes_of_johOk
  payPub_of_joh)
open H2K.First (batOneOk batOne_of_ok)

theorem atPlace_joh (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (base : ℕ) (dB : RDT)
    (dt : List RDT) (r : Fmt.M1.Stage → ℕ) (a₀ : Fmt.M1.Stage) (rest₀ : List Fmt.M1.Stage)
    (w₀ : WR) (l₀ : List WR) (c₀ : OnBytes.Slice.Chain (sgOf a₀))
    (hB : PlaceB F π num base dB dt = true) (hnum : ∀ n, num (.own (π.nums.free + n)) = base + n)
    (hj : johOk π r = true) (hs : π.nums.stages = a₀ :: rest₀)
    (hw : writtenOf π.nums = some (w₀ :: l₀))
    (hc : chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => r s.st) rest₀ a₀ l₀ = some c₀)
    (hlen : (PQ.uL (ckP .two) c₀.rds).length = (uLT (ckP .two) dt).length) :
    AtPlace F π num Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) base dB dt
      (errOfList (uLT (ckP .two) dt) (errList _ c₀.errL)) :=
  atPlace_of F π num _ _ _ _ _ base dB dt _ hB (codes_of_johOk r π hj) hnum
    (bears_own π _ _ _ _ _ dt a₀ rest₀ w₀ l₀ c₀ hs hw hc hlen)

theorem atPlaceOwn_joh (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (base : ℕ) (dB : RDT)
    (dt : List RDT) (r : Fmt.M1.Stage → ℕ) (a₀ : Fmt.M1.Stage) (rest₀ : List Fmt.M1.Stage)
    (w₀ : WR) (l₀ : List WR) (c₀ : OnBytes.Slice.Chain (sgOf a₀))
    (hB : PlaceOwnB F π num base dB dt = true)
    (hnum : ∀ n, num (.own (π.nums.free + n)) = base + n)
    (hj : johOk π r = true) (hs : π.nums.stages = a₀ :: rest₀)
    (hw : writtenOf π.nums = some (w₀ :: l₀))
    (hc : chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => r s.st) rest₀ a₀ l₀ = some c₀)
    (hlen : (PQ.uL (ckP .two) c₀.rds).length = (uLT (ckP .two) dt).length) :
    AtPlaceOwn F π num Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) base dB dt
      (errOfList (uLT (ckP .two) dt) (errList _ c₀.errL)) :=
  atPlaceOwn_of F π num _ _ _ _ _ base dB dt _ hB (codes_of_johOk r π hj) hnum
    (bears_own π _ _ _ _ _ dt a₀ rest₀ w₀ l₀ c₀ hs hw hc hlen)

/-- The second arm's three premises on "BAT"'s round, off two tests on the plan. -/
theorem own_pays (π : P12) (rad : Sg → ℕ) (r : Fmt.M1.Stage → ℕ) (hr : ∀ s, rad s = r s.st)
    (hj : johOk π r = true) (hb1 : batOneOk π = true) (dB : RDT) (dt : List RDT)
    (hl : ∃ w0 l, writtenOf π.nums = some (w0 :: l) ∧ List.Forall₂ Like (dB :: dt) (w0 :: l)) :
    PayPub π rad dB.entry.rows (batV0 π r) ∧ Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0] ∧
      dB.entry.logN ≤ 64 := by
  obtain ⟨w0, l, hw, hlike⟩ := hl
  cases hlike with
  | cons hB _ =>
    obtain ⟨h1, hlog⟩ := batOne_of_ok π w0 l hw hb1
    have hP := payPub_of_joh π r rad hr hj w0 l hw
    have hen : dB.entry = w0.entry := hB.1
    have hkd : dB.kind = w0.kind := hB.2.1
    exact ⟨by rw [hen]; exact hP, by rw [hen, hkd]; exact h1, by rw [hen]; exact hlog⟩

/-- **THE GAME AT A SEAT FROM TESTS WITH CODE**, first arm. -/
def K12GameJ : Prop :=
  ∀ (S : Type) (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rd : ℕ → ℕ) (base : ℕ)
    (dB : RDT) (dt : List RDT)
    (ext : S × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) (e : ℕ)
    (r : Fmt.M1.Stage → ℕ) (a₀ : Fmt.M1.Stage) (rest₀ : List Fmt.M1.Stage) (w₀ : WR)
    (l₀ : List WR) (c₀ : OnBytes.Slice.Chain (sgOf a₀)),
    PlaceB F π num base dB dt = true → (∀ n, num (.own (π.nums.free + n)) = base + n) →
    johOk π r = true → batOneOk π = true →
    π.nums.stages = a₀ :: rest₀ → writtenOf π.nums = some (w₀ :: l₀) →
    chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => r s.st) rest₀ a₀ l₀ = some c₀ →
    (PQ.uL (ckP .two) c₀.rds).length = (uLT (ckP .two) dt).length →
    batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e →
    (pieceOf (C := ckP .two) (F := F) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) base
        (dB :: dt) []
        ⟨ext, (e, errOfList (uLT (ckP .two) dt) (errList _ c₀.errL))⟩).ior.red.Leads
      (fun a => ∀ t, enter a.1 = .ok t → FirstOpens π num no base t)
      (fun a b => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok b.1 ∧
        QN π (NTuple F π no (fun s => r s.st) rd) (t, a.2))
      (e, errOfList (uLT (ckP .two) dt) (errList _ c₀.errL))

theorem k12_gameJ : K12GameJ := by
  intro S enter leave F W π num no rd base dB dt ext e r a₀ rest₀ w₀ l₀ c₀ hB hnum hj hb1 hs hw hc
    hlen hle
  have hA := atPlace_joh F π num base dB dt r a₀ rest₀ w₀ l₀ c₀ hB hnum hj hs hw hc hlen
  exact k12_gameSeat S enter leave F W π num no _ _ _ _ _ rd base dB dt ext e _ r hA (fun _ => rfl)
    hj hb1 hle

/-- **THE GAME AT A SEAT FROM TESTS WITH CODE**, second arm. -/
def K12GameJO : Prop :=
  ∀ (S : Type) (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rd : ℕ → ℕ) (base : ℕ)
    (dB : RDT) (dt : List RDT)
    (ext : S × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) (e : ℕ)
    (r : Fmt.M1.Stage → ℕ) (a₀ : Fmt.M1.Stage) (rest₀ : List Fmt.M1.Stage) (w₀ : WR)
    (l₀ : List WR) (c₀ : OnBytes.Slice.Chain (sgOf a₀)),
    PlaceOwnB F π num base dB dt = true → (∀ n, num (.own (π.nums.free + n)) = base + n) →
    johOk π r = true → batOneOk π = true →
    π.nums.stages = a₀ :: rest₀ → writtenOf π.nums = some (w₀ :: l₀) →
    chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => r s.st) rest₀ a₀ l₀ = some c₀ →
    (PQ.uL (ckP .two) c₀.rds).length = (uLT (ckP .two) dt).length →
    batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e →
    (pieceOf (C := ckP .two) (F := F) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) base
        (dB :: dt) []
        ⟨ext, (e, errOfList (uLT (ckP .two) dt) (errList _ c₀.errL))⟩).ior.red.Leads
      (fun a => ∀ t, enter a.1 = .ok t → FirstOpensOwn π num no base t)
      (fun a b => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok b.1 ∧
        QN π (NTuple F π no (fun s => r s.st) rd) (t, a.2))
      (e, errOfList (uLT (ckP .two) dt) (errList _ c₀.errL))

theorem k12_gameJO : K12GameJO := by
  intro S enter leave F W π num no rd base dB dt ext e r a₀ rest₀ w₀ l₀ c₀ hB hnum hj hb1 hs hw hc
    hlen hle
  have hA := atPlaceOwn_joh F π num base dB dt r a₀ rest₀ w₀ l₀ c₀ hB hnum hj hs hw hc hlen
  obtain ⟨hP, h1, hlog⟩ := own_pays π (fun s => r s.st) r (fun _ => rfl) hj hb1 dB dt hA.like
  exact k12_gameSeatO S enter leave F W π num no _ _ _ _ _ rd base dB dt ext e _ _ hA hP h1 hlog hle

/-! ## The chain's own counts as a function of the plan -/

/-- The chain that `chainFrom` gives stands over just the written rounds that it was handed. -/
theorem chainFrom_rds (X : Letters) : ∀ (rest : List Fmt.M1.Stage) (a : Fmt.M1.Stage)
    (l : List WR) (c : OnBytes.Slice.Chain (sgOf a)), chainFrom X rest a l = some c →
    c.rds = l.map WR.rd
  | [], a, l, c, hc => by
    unfold chainFrom at hc
    split at hc
    · cases hc
      rfl
    · cases hc
  | b :: rest, a, l, c, hc => by
    unfold chainFrom at hc
    split at hc
    · rename_i dE dT l'
      split at hc
      · rename_i hfc
        split at hc
        · rename_i dS dC l'' hd
          cases hn : chainFrom X rest b l'' with
          | none => rw [hn] at hc; cases hc
          | some next =>
            rw [hn] at hc
            have hc' := Option.some.inj hc
            subst hc'
            have ih := chainFrom_rds X rest b l'' next hn
            have hl : (dT :: l') = List.replicate (kk a) dT ++ dS :: dC :: l'' := by
              rw [← hfc.2, ← hd, List.take_append_drop]
            split
            · show dE.rd :: List.replicate (kk a) dT.rd ++ ([dS.rd, dC.rd] ++ next.rds) = _
              rw [ih, hl]
              simp
            · show dE.rd :: List.replicate (kk a) dT.rd ++ ([dS.rd, dC.rd] ++ next.rds) = _
              rw [ih, hl]
              simp
        · cases hc
      · cases hc
    · cases hc

theorem len_uL : ∀ ds : List PQ.RD, (PQ.uL (ckP .two) ds).length = ds.length
  | [] => rfl
  | _ :: ds => by
    show (PQ.uL (ckP .two) ds).length + 1 = ds.length + 1
    rw [len_uL ds]

theorem len_uLT : ∀ ds : List RDT, (uLT (ckP .two) ds).length = ds.length
  | [] => rfl
  | _ :: ds => by
    show (uLT (ckP .two) ds).length + 1 = ds.length + 1
    rw [len_uLT ds]

/-- **The errors behind "BAT"**: the counts of the place's own chain at the Johnson letters and the
radii r, as a list of errors over the stretch's rounds; 0 where the plan gives no chain. -/
noncomputable def errJ (π : P12) (r : Fmt.M1.Stage → ℕ) (dt : List RDT) :
    Err (uLT (ckP .two) dt) :=
  match π.nums.stages, writtenOf π.nums with
  | a :: rest, some (_ :: l) =>
    match chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => r s.st) rest a l with
    | some c => errOfList (uLT (ckP .two) dt) (errList _ c.errL)
    | none => Err.zero _
  | _, _ => Err.zero _

/-- Where the stretch is like the written rounds, these errors bear the chain's. -/
theorem bears_errJ (π : P12) (r : Fmt.M1.Stage → ℕ) (dB : RDT) (dt : List RDT)
    (hl : ∃ w0 l, writtenOf π.nums = some (w0 :: l) ∧ List.Forall₂ Like (dB :: dt) (w0 :: l)) :
    ∀ a rest w0 l (c : OnBytes.Slice.Chain (sgOf a)), π.nums.stages = a :: rest →
      writtenOf π.nums = some (w0 :: l) →
      chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => r s.st) rest a l = some c →
      Bears c.errL (errJ π r dt) := by
  intro a rest w0 l c hs hw hc
  obtain ⟨w0', l', hw', hlike⟩ := hl
  obtain ⟨rfl, rfl⟩ := List.cons.inj (Option.some.inj (hw'.symm.trans hw))
  have hlen : (PQ.uL (ckP .two) c.rds).length = (uLT (ckP .two) dt).length := by
    rw [len_uL, len_uLT, chainFrom_rds _ rest a l' c hc, List.length_map]
    cases hlike with
    | cons _ hT => exact hT.length_eq.symm
  have e : errJ π r dt = errOfList (uLT (ckP .two) dt) (errList _ c.errL) := by
    unfold errJ
    rw [hs, hw]
    dsimp only
    rw [hc]
  rw [e]
  exact bears_own π _ _ _ _ _ dt a rest w0' l' c hs hw hc hlen a rest w0' l' c hs hw hc

/-- **THE GAME AT A SEAT, ITS PUBLIC PREMISES THREE TESTS, ONE EQUATION AND ONE COMPARISON**, first
arm. -/
def K12GameT : Prop :=
  ∀ (S : Type) (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rd : ℕ → ℕ) (base : ℕ)
    (dB : RDT) (dt : List RDT)
    (ext : S × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) (e : ℕ)
    (r : Fmt.M1.Stage → ℕ),
    PlaceB F π num base dB dt = true → (∀ n, num (.own (π.nums.free + n)) = base + n) →
    johOk π r = true → batOneOk π = true →
    batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e →
    (pieceOf (C := ckP .two) (F := F) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) base
        (dB :: dt) [] ⟨ext, (e, errJ π r dt)⟩).ior.red.Leads
      (fun a => ∀ t, enter a.1 = .ok t → FirstOpens π num no base t)
      (fun a b => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok b.1 ∧
        QN π (NTuple F π no (fun s => r s.st) rd) (t, a.2))
      (e, errJ π r dt)

theorem k12_gameT : K12GameT := by
  intro S enter leave F W π num no rd base dB dt ext e r hB hnum hj hb1 hle
  have hl : likeOk π (dB :: dt) = true := by
    simp only [PlaceB, Bool.and_eq_true] at hB
    exact hB.1.1.1.1.2
  have hA := atPlace_of F π num _ _ _ _ _ base dB dt _ hB (codes_of_johOk r π hj) hnum
    (bears_errJ π r dB dt (like_of_ok π _ hl))
  exact k12_gameSeat S enter leave F W π num no _ _ _ _ _ rd base dB dt ext e _ r hA (fun _ => rfl)
    hj hb1 hle

/-- **THE GAME AT A SEAT, ITS PUBLIC PREMISES THREE TESTS, ONE EQUATION AND ONE COMPARISON**,
second arm. -/
def K12GameTO : Prop :=
  ∀ (S : Type) (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rd : ℕ → ℕ) (base : ℕ)
    (dB : RDT) (dt : List RDT)
    (ext : S × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) (e : ℕ)
    (r : Fmt.M1.Stage → ℕ),
    PlaceOwnB F π num base dB dt = true → (∀ n, num (.own (π.nums.free + n)) = base + n) →
    johOk π r = true → batOneOk π = true →
    batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e →
    (pieceOf (C := ckP .two) (F := F) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) base
        (dB :: dt) [] ⟨ext, (e, errJ π r dt)⟩).ior.red.Leads
      (fun a => ∀ t, enter a.1 = .ok t → FirstOpensOwn π num no base t)
      (fun a b => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok b.1 ∧
        QN π (NTuple F π no (fun s => r s.st) rd) (t, a.2))
      (e, errJ π r dt)

theorem k12_gameTO : K12GameTO := by
  intro S enter leave F W π num no rd base dB dt ext e r hB hnum hj hb1 hle
  have hl : likeOk π (dB :: dt) = true := by
    simp only [PlaceOwnB, Bool.and_eq_true] at hB
    exact hB.1.1.1.1.2
  have hA := atPlaceOwn_of F π num _ _ _ _ _ base dB dt _ hB (codes_of_johOk r π hj) hnum
    (bears_errJ π r dB dt (like_of_ok π _ hl))
  obtain ⟨hP, h1, hlog⟩ := own_pays π (fun s => r s.st) r (fun _ => rfl) hj hb1 dB dt hA.like
  exact k12_gameSeatO S enter leave F W π num no _ _ _ _ _ rd base dB dt ext e _ _ hA hP h1 hlog hle

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.atPlace_joh
#print axioms VerifiableInference.Desc.K12.Coin.atPlaceOwn_joh
#print axioms VerifiableInference.Desc.K12.Coin.own_pays
#print axioms VerifiableInference.Desc.K12.Coin.k12_gameJ
#print axioms VerifiableInference.Desc.K12.Coin.k12_gameJO
#print axioms VerifiableInference.Desc.K12.Coin.chainFrom_rds
#print axioms VerifiableInference.Desc.K12.Coin.bears_errJ
#print axioms VerifiableInference.Desc.K12.Coin.k12_gameT
#print axioms VerifiableInference.Desc.K12.Coin.k12_gameTO
