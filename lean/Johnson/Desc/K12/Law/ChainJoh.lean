-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.OwnMask
import Johnson.Desc.K12.Law.JohOk
import OnBytes.Slice.ManyHoldsJoh
import Cb.Bridge.GlCodesProved
/-
Johnson/Desc/K12/Law/ChainJoh.lean: K12's condition at radii below the Johnson radius: johOk's yes (Johnson/Desc/K12/Law/JohOk.lean), with pubOk's and spendOk's, gives Chain.Holds of the place's own chain at the library's Johnson letters: no fact on codes is left as a premise. Of the chain, not of the block. Nothing on hiding. **This is no proof of soundness, and no number stands in it**: see the limits.
The road. The library has Chain.holds_joh (OnBytes/Slice/ManyHoldsJoh.lean): any chain whose counts are those of the Johnson letters (Chain.PlainAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ) and whose stages, radii and rounds meet Chain.JohAt has each block taken off, under the statement on Reed–Solomon codes below the Johnson radius (Cb.BCHKS46At) as a hypothesis; that statement is a theorem at the two fields (Cb.Gl.bchks46At, Cb/Bridge/GlCodesProved.lean). RadiusLaws.lean [not in this library] lays the two together (holds_release) and writes Sg.StageJ as nine comparisons of whole numbers. This file shows that the place's own chain (Johnson/Desc/K12/Law/ChainOf.lean's chainFrom over the declared rounds) is an instance, by lemmas.
  plainAt_chainFrom     chainFrom at Letters.at L mC mS mW rad has the library's Chain.PlainAt L mC mS mW.
  RadJ · johAt_of       Chain.Pub · SpendPub · «every stage meets Sg.StageJ at its radius» ⇒ Chain.JohAt. The fold's rounds come from SpendPub (what they send and draw), not from «the round is the format's rEps»: so the place whose first fold sends its own mask is covered (johAt_step, declared nowhere in this library, asks IsRd dE (rEps …), which fails there).
  stageJ_of_L · radJ_chainFrom      from the clauses' yes to Sg.StageJ at every stage.
  holds_joh_of_ok       pubOk p K · spendOk p · johOk p r ⇒ the place's chain c at Letters.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) with c.rds = the declared rounds as written · stagesOf c = the place's stages · c.rad = r (the first stage) · c.PlainAt … · c.JohAt · c.Holds.
  k12_joh               with it the library's law on the chain, in OwnMask.lean's form.
Limits. (1) Nothing on the sizes of the counts: Sg.flC | Sg.flZ are integer parts of the library's bchksBound, which is evaluated nowhere here; with large counts Chain.Holds is true for free. «small» (K12Condition's fourth field) at these letters is open. (2) r is a letter: which radius a plan means at a stage is not said. (3) The proof of the statement on codes rests on the files under ThirdParty/, adapted from ArkLib and Mathlib (lean/LIMITS.md, L15). (4) Of the chain: hno · hacc stand as premises inside k12_joh's last conjunct. (5) The three Booleans' yes are runs' words.
Uses of the library's lemmas: Chain.holds_joh (ManyHoldsJoh.lean:135) · Cb.Gl.bchks46At (GlCodesProved.lean:20).
Nothing is left open and nothing is laid down by decree.
-/
set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK

/-- The chain's counts are the four letters': the library's Chain.PlainAt, of the place's chain at Letters.at. -/
theorem plainAt_chainFrom (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) : ∀ (rest : List Fmt.M1.Stage) (a : Fmt.M1.Stage)
    (l : List WR) (c : Chain (sgOf a)), chainFrom (.at L mC mS mW rad) rest a l = some c →
    c.PlainAt L mC mS mW
  | [], a, l, c, hc => by
    unfold chainFrom at hc
    split at hc
    · cases hc
      rfl
    · cases hc
  | b :: rest, a, l, c, hc => by
    unfold chainFrom at hc
    split at hc
    · split at hc
      · split at hc
        · rename_i dS dC l'' hd
          cases hn : chainFrom (.at L mC mS mW rad) rest b l'' with
          | none => rw [hn] at hc; cases hc
          | some next =>
            rw [hn] at hc
            have hc' := Option.some.inj hc
            subst hc'
            have ih := plainAt_chainFrom L mC mS mW rad rest b l'' next hn
            have hr : next.rad = rad (sgOf b) := rad_chainFrom _ rest b l'' next hn
            split
            · exact ⟨rfl, by rw [hr]; rfl, ih⟩
            · exact ⟨rfl, by rw [hr]; rfl, ih⟩
        · cases hc
      · cases hc
    · cases hc

/-- Every stage of the chain meets the library's condition on a stage and its radius. -/
def RadJ : {s : Sg} → Chain s → Prop
  | _, .last s e _ _ _ _ _ => s.StageJ e
  | _, .step s _ _ _ e _ _ _ _ _ _ _ _ _ next => s.StageJ e ∧ RadJ next

/-- Chain.Pub, SpendPub and RadJ give the library's Chain.JohAt. THE FOLD's ROUNDS COME FROM SpendPub (what they send and draw), NOT FROM «the round is the format's rEps»: so the arm in which the first fold sends its own mask is covered. -/
theorem johAt_of {K : Codes} : ∀ {s : Sg} (c : Chain s) (cu : IoppStage) (restI : List IoppStage),
    c.Pub K cu restI → SpendPub c → RadJ c → c.JohAt := by
  intro s c
  induction c with
  | last s e dL dB fu fs εb =>
    intro cu restI hP hS hJ
    exact ⟨hJ, ⟨_, _, hS.1⟩, hP.2.draws⟩
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    intro cu restI hP hS hJ
    obtain ⟨nx, later, _, hp, _, _, hN⟩ := hP
    exact ⟨hJ.1, hS.1, hp.rounds, ih nx later hN hS.2.2 hJ.2⟩

theorem stageJ_of_L {a : Fmt.M1.Stage} {e : ℕ} (h : ok (stageJL a e) = true) : (sgOf a).StageJ e := by
  simp only [stageJL, ok, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨⟨h1, h2, h3, h4⟩, ⟨by show 0 < a.C.r + a.C.l; omega, by show 0 < a.Z.r + a.Z.l; omega⟩, h5, h6, h7,
    h8, h9⟩

theorem radJ_chainFrom (X : Letters) (r : Fmt.M1.Stage → ℕ) (hX : ∀ s, X.rad s = r s.st) :
    ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (a : Fmt.M1.Stage) (l : List WR) (c : Chain (sgOf a)),
    chainFrom X rest a l = some c → ok (johWalk r j (a :: rest)) = true → RadJ c
  | [], j, a, l, c, hc, h => by
    unfold chainFrom at hc
    split at hc
    · cases hc
      unfold johWalk at h
      rw [ok_append, ok_tag, Bool.and_eq_true] at h
      show (sgOf a).StageJ (X.rad (sgOf a))
      rw [hX]
      exact stageJ_of_L h.1
    · cases hc
  | b :: rest, j, a, l, c, hc, h => by
    unfold chainFrom at hc
    split at hc
    · split at hc
      · split at hc
        · rename_i dS dC l'' hd
          cases hn : chainFrom X rest b l'' with
          | none => rw [hn] at hc; cases hc
          | some next =>
            rw [hn] at hc
            have hc' := Option.some.inj hc
            subst hc'
            unfold johWalk at h
            rw [ok_append, ok_tag, Bool.and_eq_true] at h
            have ih := radJ_chainFrom X r hX rest (j + 1) b l'' next hn h.2
            have h1 : (sgOf a).StageJ (X.rad (sgOf a)) := by
              rw [hX]
              exact stageJ_of_L h.1
            split
            · exact ⟨h1, ih⟩
            · exact ⟨h1, ih⟩
        · cases hc
      · cases hc
    · cases hc

/-- AT A PLACE, AT RADII BELOW THE JOHNSON RADIUS: pubOk's, spendOk's and johOk's yes give the place's own chain over its declared rounds, at the library's Johnson letters (Sg.lstJ · Sg.flC · Sg.flZ · Sg.flZ) and the radii r, with Chain.PlainAt, Chain.JohAt AND Chain.Holds: by the library's Chain.holds_joh with the theorem on codes (Cb.Gl.bchks46At) laid in. -/
theorem holds_joh_of_ok (r : Fmt.M1.Stage → ℕ) (p : P12) (K : Codes) (hp : pubOk p K = true)
    (hs : spendOk p = true) (hj : johOk p r = true) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧
      chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => r s.st) rest a l = some c ∧
      c.rds = l.map WR.rd ∧ stagesOf c = p.nums.stages ∧ c.rad = r (stN a) ∧
      c.PlainAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ ∧ c.JohAt ∧ c.Holds := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, e6⟩ :=
    pub_of_ok (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => r s.st) p K hp
  obtain ⟨cu, restI, f1, f2⟩ : ∃ cu restI, stageAt p 0 a = some cu ∧ stagesAt p 1 rest = some restI := by
    unfold pubOk pubL at hp
    rw [e1, e2] at hp
    exact walk_forms p K rest 0 a l hp
  have hP := plainAt_chainFrom Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) rest a l c e3
  have hR : RadJ c := radJ_chainFrom _ r (fun _ => rfl) rest 0 a l c e3 (by
    unfold johOk johAll at hj
    rw [e1] at hj
    exact hj)
  have hJ := johAt_of c cu restI (e6 a rest cu restI e1 f1 f2) (spend_of_ok _ p hs a rest w0 l c e1 e2 e3) hR
  exact ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, rad_chainFrom _ rest a l c e3, hP, hJ,
    c.holds_joh Cb.Gl.bchks46At hP hJ⟩

/-- With it the library's law on the chain (OwnMask.lean's form). OF THE CHAIN, NOT OF THE BLOCK; NO BOUND ON THE COUNTS. -/
theorem k12_joh (r : Fmt.M1.Stage → ℕ) (p : P12) (K : Codes) (hp : pubOk p K = true)
    (hs : spendOk p = true) (hj : johOk p r = true) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧
      chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => r s.st) rest a l = some c ∧
      c.rds = l.map WR.rd ∧ stagesOf c = p.nums.stages ∧ c.rad = r (stN a) ∧ c.Holds ∧
      ∀ (q : GE × ((sgOf a).cIn.J → GE)) (y : (sgOf a).cIn.Word) (fz : Msg1 c → (sgOf a).cFr.Word)
        (g : (sgOf a).cIn.Word), (∀ w, ¬ (sgOf a).RIn c.rad (q, y) w) →
        ∀ acc : Tr (PQ.uL (ckP .two) c.rds) → Bool,
          (∀ b, acc (c.trL b) = true → c.Acc q y (fz (msg1 c b)) g b ∧
            PQ.passSL (ckP .two) c.rds (PQ.rhoSL (ckP .two) c.rds (c.trL b)) = true) →
          Doomed (PQ.uL (ckP .two) c.rds) c.errL fun τ => acc τ = false := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, e6, _, _, hH⟩ := holds_joh_of_ok r p K hp hs hj
  exact ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, e6, hH,
    fun q y fz g hno acc hacc => chain_many_list_own c hH q y fz g hno acc hacc⟩

end H2K.Pub

#print axioms H2K.Pub.holds_joh_of_ok
#print axioms H2K.Pub.k12_joh
