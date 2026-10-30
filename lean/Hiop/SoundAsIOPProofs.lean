-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/SoundAsIOPProofs.lean: the proofs of four statements of Hiop/SoundAsIOP.lean:
soundInParts_iff_soundAtR, wholeRunSound_of_soundInParts, wholeRunState_laws,
wholeRunSound_of_indexKnowledgeSoundIOP. For every object L : HolographicProtocol.

How the whole run is joined. Each part is a list of rounds; "the prover has lost in s ++ t" follows
from "it has lost in s towards: it has lost in t" (Doomed.append, Iop/Rbr.lean). A round in which the
prover alone speaks (the answer, the named request) has the error 0. At a table's round the bad
challenges are the points with a collision. At a part's rounds: either the part's own clause says that
the prover has lost towards "this verifier rejects", and then the conclusion holds for want of an
accepting transcript; or what the part is to show holds already, and the prover has lost in the part's
rounds for free, towards "it has lost in what follows".
-/
import Hiop.SoundAsIOP

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace Iop
open Prob Blocks BatchK

variable {Index Request : Type}

/-! ## Tools on lists of rounds -/

/-- Two lists of rounds in a row, the goal given by parts. -/
theorem doomed_append_parts (s t : Shape) (ε : Err s) (ε' : Err t) (goal : Tr s → Tr t → Prop)
    (h : Doomed s ε fun a => Doomed t ε' (goal a)) :
    Doomed (s ++ t) (Err.app ε ε') fun τ => goal (Tr.fst τ) (Tr.snd (s := s) τ) :=
  Doomed.append s t ε ε' _ (Doomed.mono s ε (fun a ha => Doomed.mono t ε' (fun b hb => by
    show goal (Tr.fst (Tr.app a b)) (Tr.snd (s := s) (Tr.app a b))
    rw [Tr.fst_app, Tr.snd_app]
    exact hb) ha) h)

/-- A part with a verifier, then what follows. The goal holds wherever the part's verifier rejects.
Either the prover has lost in the part towards rejection, or it has lost in what follows whatever the
part's transcript. -/
theorem doomed_part (s t : Shape) (ε : Err s) (ε' : Err t) (accept : Tr s → Bool)
    (goal : Tr s → Tr t → Prop) (free : ∀ a b, accept a = false → goal a b)
    (h : Doomed s ε (fun a => accept a = false) ∨ ∀ a, Doomed t ε' (goal a)) :
    Doomed (s ++ t) (Err.app ε ε') fun τ => goal (Tr.fst τ) (Tr.snd (s := s) τ) :=
  doomed_append_parts s t ε ε' goal <| h.elim
    (fun h1 => Doomed.mono s ε (fun a ha => Doomed.of_forall t ε' fun b => free a b ha) h1)
    (fun h2 => Doomed.of_forall s ε h2)

/-- A round in which the prover says something in the clear and the verifier sends nothing. -/
theorem doomed_said {Said : Type} (said0 : Said) (s : Shape) (ε : Err s) (goal : Said → Tr s → Prop)
    (h : ∀ said, Doomed s ε (goal said)) :
    Doomed (plainRound Said Unit said0 :: s) (0, ε) fun τ => goal τ.1.2 τ.2.2 := by
  intro m
  refine le_of_eq (cnt_false fun u hu => hu ?_)
  exact h m.2

/-- A bound on a list in which the shared rounds' errors are counted several times bounds the list. -/
theorem Err.Below.of_timesShared {n : ℕ} (hn : 0 < n) :
    ∀ {s : Shape} {A : RoundSplits s} {ε : Err s} {c : ℝ≥0∞},
      Err.Below (Err.timesShared n A ε) c → Err.Below ε c
  | [], _, _, _, _ => trivial
  | _ :: _, (a, _), (e, _), _, h => by
      refine ⟨_root_.le_trans (Nat.cast_le.2 ?_) h.1, Err.Below.of_timesShared hn h.2⟩
      cases a.kind
      · exact Nat.le_mul_of_pos_left e hn
      · exact le_rfl

namespace HolographicProtocol

/-- A table and its out-of-domain sample in front of a game: if few points give a collision, and
without a collision the prover has lost the rest, it has lost the whole. -/
theorem doomed_table (L : HolographicProtocol Index Request) (fill : L.Fill) (s : Shape) (e : ℕ) (ε : Err s)
    (goal : L.Table → L.Sample → Tr s → Prop)
    (few : ∀ table : L.Table, cnt (fun point => L.hasCollisionAt table point) ≤ e)
    (h : ∀ (table : L.Table) (sample : L.Sample), ¬ L.hasCollisionAt table sample.1 →
      Doomed s ε (goal table sample)) :
    Doomed (L.tableRounds fill ++ s) (e, 0, ε) fun τ =>
      goal τ.1.1 (τ.2.1, τ.2.2.1.2) τ.2.2.2.2 := by
  intro m
  refine le_trans (cnt_mono fun point hpoint => ?_) (few m.1)
  by_contra hn
  apply hpoint
  intro m2
  refine le_of_eq (cnt_false fun u hu => hu ?_)
  exact h m.1 (point, m2.2) hn

/-- The online part for one request, of which the part that is fixed first is named before the
rounds. -/
theorem online_one (L : HolographicProtocol Index Request) (relation : Index → Request → Prop)
    (errors : L.RoundErrors) (late : L.late = none) (place : 0 < L.maxBatchSize)
    (h : L.SoundInParts relation errors) (copy : L.Table) (copySample : L.Sample)
    (named : Request) :
    Doomed L.onlineBatch.loc.shape errors.online fun τ =>
      ∀ request, L.early request = L.early named →
        L.onlineBatch.loc.accept (request, copySample) copy τ = true →
        ∀ index, L.decodeIndex copy copySample = some index → relation index request := by
  obtain ⟨-, State, h1, h2, -, h4, h5⟩ :=
    (sndBP_laws Request _ (L.batAt copySample) L.maxBatchSize L.early L.late _ errors.online).1
      (h.online copySample)
  refine doomed_of_jointLaw ⟨0, place⟩ _ (L.batAt copySample).ann errors.online _
    (State copy (L.early named)) _ rfl (h2 copy _) (h5 copy fun _ => some (L.early named))
    (h1 copy named) ?_
  intro τ hτ request he ha
  refine h4 copy request τ ?_ ha
  rw [late]
  show State copy (L.early request) (.full τ) = false
  rw [he]
  exact hτ

/-- The conclusion, by the parts of a whole run. -/
def concludesAt (L : HolographicProtocol Index Request) (relation : Index → Request → Prop) (firstTable : L.Table)
    (firstSample : L.Sample) (offline : Tr L.offline.shape) (copy : L.Table) (copySample : L.Sample)
    (link : Tr L.link.shape) (named : Request) (online : Tr L.onlineBatch.loc.shape) : Prop :=
  (⟨firstTable, firstSample, offline, copy, copySample, link, named, online⟩ :
    L.WholeRun).Concludes relation

/-- The rounds from the named request on. -/
abbrev onlineRounds (L : HolographicProtocol Index Request) (fill : L.Fill) : Shape :=
  plainRound Request Unit fill.request :: L.onlineBatch.loc.shape

/-- The rounds from the copy on. -/
abbrev copyRounds (L : HolographicProtocol Index Request) (fill : L.Fill) : Shape :=
  L.tableRounds fill ++ (L.link.shape ++ L.onlineRounds fill)

end HolographicProtocol

/-! ## The statements -/

theorem soundInParts_iff_soundAtR : Spec.soundInParts_iff_soundAtR := by
  intro Index Request L relation errors
  constructor
  · intro h
    refine ⟨h.nothingAtCollision, h.samplePoint, ?_, ?_, ?_⟩
    · intro sample table hn
      rw [not_or, not_not] at hn
      exact h.offline table sample hn.1 hn.2
    · intro rr y hn
      rw [not_or, not_or] at hn
      obtain ⟨index, hi⟩ := Option.ne_none_iff_exists'.1 hn.1
      exact h.link y.1 y.2 rr.1 rr.2 index hi hn.2.1 fun hc => hn.2.2 (hc.trans hi.symm)
    · intro sample
      refine sndBP_mono Request _ (L.batAt sample) L.maxBatchSize L.early L.late _ _ errors.online ?_
        (h.online sample)
      intro request copy τ _ hok
      show L.decodeIndex copy sample = none ∨ ∃ i, L.decodeIndex copy sample = some i ∧ relation i request
      cases hd : L.decodeIndex copy sample with
      | none => exact Or.inl rfl
      | some i => exact Or.inr ⟨i, rfl, hok i hd⟩
  · intro h
    refine ⟨h.noneColl, h.rcd, ?_, ?_, ?_⟩
    · intro table sample hc hd
      exact h.sndT sample table fun hh => hh.elim hc fun h2 => h2 hd
    · intro firstTable copy firstSample copySample index hi hc hd
      refine h.sndL (firstSample, copySample) (firstTable, copy) fun hh => ?_
      have hi' : L.decodeIndex firstTable firstSample = some index := hi
      rcases hh with h1 | h1 | h1
      · exact Option.some_ne_none index (hi'.symm.trans h1)
      · exact hc h1
      · exact hd (h1.trans hi')
    · intro sample
      refine sndBP_mono Request _ (L.batAt sample) L.maxBatchSize L.early L.late _ _ errors.online ?_
        (h.sndB sample)
      intro request copy τ _ hok index hd
      have hok' : L.decodeIndex copy sample = none ∨
          ∃ i, L.decodeIndex copy sample = some i ∧ relation i request := hok
      rcases hok' with h1 | ⟨i, h1, h2⟩
      · exact absurd (hd.symm.trans h1) (Option.some_ne_none index)
      · obtain rfl : index = i := Option.some.inj (hd.symm.trans h1)
        exact h2

theorem wholeRunSound_of_soundInParts : Spec.wholeRunSound_of_soundInParts := by
  intro Index Request L relation errors fill late place h
  -- from the named request on: the copy decodes to the extracted index
  have hOnline : ∀ (t0 : L.Table) (s0 : L.Sample) (a : Tr L.offline.shape) (t1 : L.Table)
      (s1 : L.Sample) (b : Tr L.link.shape) (index : Index),
      L.extractIndex t0 s0 = some index → L.decodeIndex t1 s1 = some index →
      Doomed (L.onlineRounds fill) (0, errors.online) fun τ =>
        L.concludesAt relation t0 s0 a t1 s1 b τ.1.2 τ.2.2 := by
    intro t0 s0 a t1 s1 b index h0 h1
    refine doomed_said fill.request _ errors.online
      (fun named c => L.concludesAt relation t0 s0 a t1 s1 b named c) fun named => ?_
    refine Doomed.mono _ _ ?_ (L.online_one relation errors late place h t1 s1 named)
    intro c hc request he hacc
    exact ⟨index, h0, h1, hc request he hacc.2.2 index h1⟩
  -- the link's rounds
  have hLink : ∀ (t0 : L.Table) (s0 : L.Sample) (a : Tr L.offline.shape) (index : Index),
      L.extractIndex t0 s0 = some index → ∀ (t1 : L.Table) (s1 : L.Sample), ¬ L.hasCollisionAt t1 s1.1 →
      Doomed (L.link.shape ++ L.onlineRounds fill)
        (Err.app (s := L.link.shape) (t := L.onlineRounds fill) errors.link (0, errors.online))
        fun τ => L.concludesAt relation t0 s0 a t1 s1 (Tr.fst τ)
          (Tr.snd (s := L.link.shape) τ).1.2 (Tr.snd (s := L.link.shape) τ).2.2 := by
    intro t0 s0 a index h0 t1 s1 hc
    refine doomed_part L.link.shape (L.onlineRounds fill) errors.link (0, errors.online)
      (fun b => L.link.accept (s0, s1) (t0, t1) b)
      (fun b τ => L.concludesAt relation t0 s0 a t1 s1 b τ.1.2 τ.2.2) ?_ ?_
    · intro b τ hb request _ hacc
      exact absurd (hb.symm.trans hacc.2.1) Bool.false_ne_true
    · by_cases hd : L.decodeIndex t1 s1 = some index
      · exact Or.inr fun b => hOnline t0 s0 a t1 s1 b index h0 hd
      · exact Or.inl (h.link t0 t1 s0 s1 index h0 hc hd)
  -- the copy and its sample
  have hCopy : ∀ (t0 : L.Table) (s0 : L.Sample) (a : Tr L.offline.shape) (index : Index),
      L.extractIndex t0 s0 = some index →
      Doomed (L.copyRounds fill)
        (errors.samplePoint, 0,
          Err.app (s := L.link.shape) (t := L.onlineRounds fill) errors.link (0, errors.online))
        fun τ => L.concludesAt relation t0 s0 a τ.1.1 (τ.2.1, τ.2.2.1.2) (Tr.fst τ.2.2.2.2)
          (Tr.snd (s := L.link.shape) τ.2.2.2.2).1.2 (Tr.snd (s := L.link.shape) τ.2.2.2.2).2.2 := by
    intro t0 s0 a index h0
    exact L.doomed_table fill (L.link.shape ++ L.onlineRounds fill) errors.samplePoint _
      (fun t1 s1 rest => L.concludesAt relation t0 s0 a t1 s1 (Tr.fst rest)
        (Tr.snd (s := L.link.shape) rest).1.2 (Tr.snd (s := L.link.shape) rest).2.2)
      h.samplePoint (hLink t0 s0 a index h0)
  -- the offline rounds
  have hOffline : ∀ (t0 : L.Table) (s0 : L.Sample), ¬ L.hasCollisionAt t0 s0.1 →
      Doomed (L.offline.shape ++ L.copyRounds fill)
        (Err.app (s := L.offline.shape) (t := L.copyRounds fill) errors.offline
          (errors.samplePoint, 0,
            Err.app (s := L.link.shape) (t := L.onlineRounds fill) errors.link (0, errors.online)))
        fun τ => (fun (a : Tr L.offline.shape) (σ : Tr (L.copyRounds fill)) =>
          L.concludesAt relation t0 s0 a σ.1.1 (σ.2.1, σ.2.2.1.2) (Tr.fst σ.2.2.2.2)
            (Tr.snd (s := L.link.shape) σ.2.2.2.2).1.2 (Tr.snd (s := L.link.shape) σ.2.2.2.2).2.2)
          (Tr.fst τ) (Tr.snd (s := L.offline.shape) τ) := by
    intro t0 s0 hc
    refine doomed_part L.offline.shape (L.copyRounds fill) errors.offline
      (errors.samplePoint, 0,
        Err.app (s := L.link.shape) (t := L.onlineRounds fill) errors.link (0, errors.online))
      (fun a => L.offline.accept s0 t0 a)
      (fun (a : Tr L.offline.shape) (σ : Tr (L.copyRounds fill)) =>
        L.concludesAt relation t0 s0 a σ.1.1 (σ.2.1, σ.2.2.1.2) (Tr.fst σ.2.2.2.2)
          (Tr.snd (s := L.link.shape) σ.2.2.2.2).1.2 (Tr.snd (s := L.link.shape) σ.2.2.2.2).2.2)
      ?_ ?_
    · intro a σ ha request _ hacc
      exact absurd (ha.symm.trans hacc.1) Bool.false_ne_true
    · cases h0 : L.extractIndex t0 s0 with
      | none => exact Or.inl (h.offline t0 s0 hc h0)
      | some index => exact Or.inr fun a => hCopy t0 s0 a index h0
  -- the first table and its sample
  exact L.doomed_table fill (L.offline.shape ++ L.copyRounds fill) errors.samplePoint _
    (fun t0 s0 rest => (fun (a : Tr L.offline.shape) (σ : Tr (L.copyRounds fill)) =>
      L.concludesAt relation t0 s0 a σ.1.1 (σ.2.1, σ.2.2.1.2) (Tr.fst σ.2.2.2.2)
        (Tr.snd (s := L.link.shape) σ.2.2.2.2).1.2 (Tr.snd (s := L.link.shape) σ.2.2.2.2).2.2)
      (Tr.fst rest) (Tr.snd (s := L.offline.shape) rest))
    h.samplePoint hOffline

theorem wholeRunState_laws : Spec.wholeRunState_laws := by
  intro Index Request L relation errors fill h
  exact ⟨(lost_empty _ _ _).2 h, fun τ m => Lost.prover _ _ _ τ m, fun τ => Lost.verifier _ _ _ τ,
    fun τ => lost_full _ _ _ τ⟩

theorem wholeRunSound_of_indexKnowledgeSoundIOP : Spec.wholeRunSound_of_indexKnowledgeSoundIOP := by
  intro Index Request L relation offlineMarks offlinePlaces linkMarks linkPlaces bound fill late place
    hT hL
  rintro ⟨errors, within, parts⟩
  refine ⟨errors, ?_, wholeRunSound_of_soundInParts Index Request L relation errors fill late place
    parts⟩
  have zero : ∀ k : ℝ≥0∞, ((0 : ℕ) : ℝ≥0∞) ≤ bound * k := fun k => by simp
  exact ⟨within.samplePoint, zero _, Err.Below.app (Err.Below.of_timesShared hT within.offline)
    ⟨within.samplePoint, zero _, Err.Below.app (Err.Below.of_timesShared hL within.link)
      ⟨zero _, within.online⟩⟩⟩

end Iop

#print axioms Iop.soundInParts_iff_soundAtR
#print axioms Iop.wholeRunSound_of_soundInParts
#print axioms Iop.wholeRunState_laws
#print axioms Iop.wholeRunSound_of_indexKnowledgeSoundIOP
