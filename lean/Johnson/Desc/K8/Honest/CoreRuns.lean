-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/CoreRuns.lean: EACH RUN OF CLAIMS OF THE THREE SORTS OF SEGMENT, BUT FOR
"K8.equations", LEAVES THE TEN FIELDS OF THE LEDGER THAT `SameCore`
(Johnson/Desc/K8/Honest/SameCore.lean) NAMES. Statements and proofs. No prover. Lemmas; none of the
library's goals.

  `KeepsCore f`   where the run f returns and the batching's lens finds a part in front, it finds
      one behind, and the ledger behind has the ledger's ten fields in front: the clause "ledger" of
      `PlainRun` and `PlainBehind` (Johnson/Desc/K8/Honest/PlainRuns.lean), said of `SameCore`
  `core_putFork`, `core_back`   a ledger laid by putFork; a run that hands the state back
  `core_idle`, `core_objects`, `core_flRun`, `core_join`, `core_planes`, `core_still`   the run
      without a claim; the lookup's "objects", "join", "planes"; a run of forms that hands the state
      back
  `core_front`, `core_behind`   the feed-forward kind's two runs
  `core_first`, `core_keys`, `core_second`   attention's three
  `core_runsBy`, `core_k6`, `core_merge`   the output head's own runs; the merge's
The arguments are those of the clause "ledger" in PlainRuns.lean, FallAtt.lean and FallHead.lean,
with `SameCore` in the place of `SameSums`.
Limits. Which ten fields, and which five are not carried: SameCore.lean's head. Nothing on whether a
run returns, nor on its claims.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.SameCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.K.Kc
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.Kinds.Head
open Johnson.Desc.First.ForkMerge (headMergeClaim)
open OnBytes.Desc.First.K4 (frontAtC backAtC formsFrontWith_core formsBack_core Wrote blockAtC)

/-- The run leaves the ledger's ten fields. -/
def KeepsCore (f : Nat → S → Except String (List Claim × S)) : Prop :=
  ∀ n t y a, f n t = .ok y → K9.atS.get? t = some a →
    ∃ b, K9.atS.get? y.2 = some b ∧ SameCore a.F b.F

theorem core_putFork (t : S) (a : K9.Part) (F G : Fork) (h : K9.atS.get? t = some a)
    (hF : t.fork? = some F) (hs : SameCore F G) :
    ∃ b, K9.atS.get? (t.putFork G) = some b ∧ SameCore a.F b.F := by
  obtain ⟨u, hb⟩ := K9.get_putFork' t a G h
  obtain rfl : a.F = F := Option.some.inj ((K9.get_fork t a h).symm.trans hF)
  exact ⟨_, hb, hs⟩

/-- A run that hands the state back. -/
theorem core_back {f : Nat → S → Except String (List Claim × S)}
    (h : ∀ n t y, f n t = .ok y → y.2 = t) : KeepsCore f := fun n t y a hy ha => by
  rw [h n t y hy]
  exact ⟨a, ha, SameCore.refl _⟩

theorem core_idle : KeepsCore LinkJoin.idle0 :=
  core_back fun n t y h => by
    obtain rfl : (([] : List Claim), t) = y := Except.ok.inj h
    rfl

theorem core_objects (heard : S → Option Forest.Heard) : KeepsCore (K9.objectsBy heard) :=
  fun n t y a h ha => by
    obtain ⟨c, e⟩ := y
    obtain ⟨F, g, hF, hg, rfl, rfl⟩ := objectsBy_ok heard n t e c h
    exact core_putFork t a F _ ha hF (SameCore.paid F _)

theorem core_flRun {β γ δ : Type} (e0 : String) (pre1 : S → Except String β) (e1 : String)
    (test : β → Fork → Bool) (pre2 : S → Except String γ) (e2 : String) (m : β → γ → Fl δ)
    (out : δ → List Claim) (hm : ∀ b c, FlCore (m b c)) :
    KeepsCore (K9.flRun e0 pre1 e1 test pre2 e2 m out) := by
  intro n t y a h ha
  unfold K9.flRun at h
  obtain ⟨F, hF, h⟩ := K9L.ok_bind h
  obtain ⟨b, hb, h⟩ := K9L.ok_bind h
  obtain ⟨_, hte, h⟩ := K9L.ok_bind h
  obtain ⟨c, hc, h⟩ := K9L.ok_bind h
  obtain ⟨x, hx, h⟩ := K9L.ok_bind h
  obtain rfl := Except.ok.inj h
  exact core_putFork t a F _ ha (named_ok hF) (hm b c F [] x (named_ok hx))

theorem core_join (keys : S → Option (Array Aff)) : KeepsCore (K9.joinCalls keys) :=
  core_flRun _ _ _ _ _ _ _ _ fun g KF => joinF_core g KF

theorem core_planes (lm : Nat) (readers : K3.Readers S) :
    KeepsCore (K9.planesCalls lm readers) :=
  core_flRun _ _ _ _ _ _ _ _ fun g r => planesProg_core lm g r

theorem core_still (nm : String) (K : S → Option (List Aff × S))
    (hK : ∀ t z, K t = some z → z.2 = t) :
    KeepsCore fun _ s => (named nm (K s)).map fun y => (y.1.map K9.ofForm, y.2) :=
  core_back fun n t y h => by
    cases hk : K t with
    | none =>
      rw [hk] at h
      exact absurd h (by simp [named, Except.map])
    | some z =>
      rw [hk] at h
      have e : (z.1.map K9.ofForm, z.2) = y := Except.ok.inj h
      rw [← e]
      exact hK t z hk

/-! ## The feed-forward kind's two runs -/

theorem wrote_core {t t' : S} {a : LayOwn} {G : Fork} (w : Wrote t a G t')
    (hs : SameCore a.F G) :
    ∀ x, K9.atS.get? t = some x → ∃ b, K9.atS.get? t' = some b ∧ SameCore x.F b.F := by
  obtain ⟨h1, h2⟩ := wrote_here w
  intro x hx
  obtain ⟨b, hb, hbF⟩ := lay_part t' _ h2
  have hxF : x.F = a.F := Option.some.inj ((K9.get_fork t x hx).symm.trans (lay_fork t a h1))
  exact ⟨b, hb, by rw [hbF, hxF]; exact hs⟩

theorem core_front (p : OnBytes.Desc.First.K4.Par)
    (r : Nat → S → Except String (List Claim × S))
    (hr : (blockAtC p).claims.lookup "front" = some r) : KeepsCore r := by
  intro n t y x h hx
  obtain ⟨c, e⟩ := y
  obtain ⟨a, o, fs, G, ho, hf, rfl, w⟩ := frontAtC hr h
  rw [frontOf_eq] at hf
  exact wrote_core w (SameCore.ofCore (formsFrontWith_core hf)) x hx

theorem core_behind (p : OnBytes.Desc.First.K4.Par)
    (r : Nat → S → Except String (List Claim × S))
    (hr : (blockAtC p).claims.lookup "back" = some r) : KeepsCore r := by
  intro n t y x h hx
  obtain ⟨c, e⟩ := y
  obtain ⟨a, o, fs, G, ho, hf, rfl, w⟩ := backAtC hr h
  exact wrote_core w (SameCore.ofCore (formsBack_core hf)) x hx

/-! ## Attention's three runs -/

theorem core_first (c : P.ParC) : KeepsCore (K5Law.runFirst c) :=
  core_still "K5.first" (P.firstK (P.seatCO c) c) fun t z h => by
    unfold P.firstK at h
    obtain ⟨⟨i, K⟩, -, h⟩ := Option.bind_eq_some_iff.1 h
    dsimp only at h
    obtain ⟨r, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj h
    rfl

theorem core_keys (c : P.ParC) : KeepsCore (K5Law.runKeys c) :=
  core_still "K5.keys" (P.keysK (P.seatCO c) c) fun t z h => by
    unfold P.keysK at h
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl

theorem core_second (c : P.ParC) : KeepsCore (K5Law.runSecond c) :=
  core_still "K5.second" (P.secondK (P.seatCO c) c) fun t z h => by
    unfold P.secondK at h
    obtain ⟨⟨i, K⟩, -, h⟩ := Option.bind_eq_some_iff.1 h
    dsimp only at h
    obtain ⟨r, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj h
    rfl

/-! ## The output head's own runs; the merge's -/

theorem core_runsBy (names : List String)
    (runs : Given → Behind → Places → List (String × List Kinds.Form))
    (keys : Given → Behind → Places → List Kinds.Form) (p : Kinds.Head.Par)
    (h : Model.Head.Shape) (iU3 : Nat)
    (name : String) (r : Nat → S → Except String (List Claim × S))
    (hr : (runsBy names runs keys asClaim p (seatAt h iU3)).lookup name = some r) :
    KeepsCore r := by
  unfold runsBy at hr
  obtain rfl := lookup_map _ names name r hr
  refine core_back fun n t y hy => ?_
  obtain ⟨⟨g, b, x⟩, hl, hy⟩ := K9L.ok_bind hy
  dsimp only at hy
  obtain ⟨fs, hfs, hy⟩ := K9L.ok_bind hy
  rw [← Except.ok.inj hy]
  cases (names.head? == some name) <;> rfl

theorem core_k6 (h : Model.Head.Shape) (iU3 l piece : Nat) (p : Kinds.Head.Par) (name : String)
    (r : Nat → S → Except String (List Claim × S))
    (hr : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some r) : KeepsCore r := by
  dsimp only [kind] at hr
  exact core_runsBy _ _ _ p h iU3 name r hr

theorem core_merge : KeepsCore headMergeClaim := by
  intro n t y q h hq
  obtain ⟨a, wo, x, ha, hwo, hx, rfl⟩ := merge_cut n t y h
  have hF := K9.get_fork t q hq
  have ho : a.opened = true := by
    unfold S.fork? at hF
    rw [ha] at hF
    by_cases ho : a.opened = true
    · exact ho
    · simp [ho] at hF
  have hFa : t.fork? = some a.F := by
    unfold S.fork?
    rw [ha]
    simp [ho]
  have hput : ({ t with here := .head { a with F := x.2.1 } } : S) = t.putFork x.2.1 := by
    unfold S.putFork
    rw [ha]
    simp [ho]
  rw [hput]
  exact core_putFork t q a.F _ hq hFa (pscRow_core wo.p wo.fvp {} a.F [] x hx)

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.core_objects
#print axioms VerifiableInference.Desc.First.K8.Honest.core_join
#print axioms VerifiableInference.Desc.First.K8.Honest.core_planes
#print axioms VerifiableInference.Desc.First.K8.Honest.core_front
#print axioms VerifiableInference.Desc.First.K8.Honest.core_behind
#print axioms VerifiableInference.Desc.First.K8.Honest.core_first
#print axioms VerifiableInference.Desc.First.K8.Honest.core_keys
#print axioms VerifiableInference.Desc.First.K8.Honest.core_second
#print axioms VerifiableInference.Desc.First.K8.Honest.core_k6
#print axioms VerifiableInference.Desc.First.K8.Honest.core_merge
