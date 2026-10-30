-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/ObjectsOn.lean: THE SENTENCE "the forms of a run are worth 0, in front of
the segment's second sending" (`formsTQ`, Johnson/Desc/Sound/FormsQ.lean) GOES FORWARD OVER A YES OF
THE SUB-PROTOCOL "the output head's own rounds" (K6), at the lookup's two runs "objects" and
"guests": from the verifier's state in front to the state behind, at one witness. AT TWO STATES: no
meaning, no piece of the proof of soundness, no string of a file. EVERY THEOREM IS CONDITIONAL.

Why. The library carries that sentence BACK over the sub-protocol (`kept_back`,
Johnson/Desc/Kinds/Law/K6RidersAtMgAll.lean) and its public test forward (`kept_on`,
Johnson/Desc/Kinds/Law/K6ObjectsKept.lean): what a proof of soundness wants. An honest prover's
invariant holds the sentence of every open claim at its own witness, and must carry it forward.

  `formsTQ_on`       the mirror of the library's `formsTQ_rides` (Johnson/Desc/Sound/FormsQ.lean),
                     general in the readers, the stated data, the run and the two states.
                     CONDITIONAL: both states have their parts; what the reader answers in front it
                     answers behind; the public test BEHIND; the later part rides on the earlier
                     one; the stated data agree at what the forms name; the sentence in front
  `K6Keeps.shape`    what `K6Keeps` (Honest/Law/Keeps.lean) says of the state behind, written out.
                     CONDITIONAL: K
  `k6_reads_fwd`     what the segment's reader answers in front it answers behind.
                     CONDITIONAL: hS, hB, hn, ho, hop, hg, hbare
  `k6_stated_at`     the stated data agree at both states at what the reader's forms name.
                     CONDITIONAL: hS, hn, ho, hop, hbare
  `kept_fwd`         THE MIRROR OF `kept_back`. CONDITIONAL: hS, hB, hn, ho, hop, hL, hSz, hg,
                     hbare, and the sentence in front
  `kept_fwd_keeps`   the same at `K6Keeps` and the public test on the ledger's sizes.
                     CONDITIONAL: hS, hB, hn, K, hled, hg, hbare, and the sentence in front

What is called and what is typed anew. Called: `value_ridesW` (a form is worth the same at two
parts; its premises speak of the earlier part, so it serves both ways), `formsTQ_in` (the sentence
holds its test: Johnson/Desc/Sound/BordersForms.lean), `readers_kept`, `segAt_head`,
`readers_kept_on`, `kept_on`, `sized_iff` (Johnson/Desc/Kinds/Law/GrowsAt.lean), `Fwd`
(Johnson/Desc/Reads/FormsPass.lean). Typed anew: `formsTQ_on` follows the proof of
`formsTQ_rides` line by line with the ends changed; `k6_stated_at` and the clause on the later part
in `kept_fwd` follow two bullets of the proof of `kept_back`. The library has no lemma that carries
`formsTQ` forward; its `formsTQ_same` (Johnson/Desc/Sound/Foot/FormsQSame.lean) asks that the open
segment's part be the same at both states, which fails here: the ledger turns. A NEAR TWIN OF
`formsTQ_on` stands in a file on the first chain's thread: `formsTQ_fwd_test`
(Johnson/Desc/ProofFile/Honest/Thread/FormsTLater.lean): the same end from the same premises but
two: it asks two of the seven fields of `Rides`, and `StatedSame` where hat stands here. It is not
imported: this file imports no file on the thread.

`k6_stated_at` ends in the text of the library's `StatedSame`
(Johnson/Desc/K1/Law/GoAtLaterForms.lean), written out, so that that file need not be imported.

Limits.
  - THAT THE PREMISES CAN BE MET TOGETHER: NO EXAMPLE. hS, hB: on the IOP as written in Lean. hbare:
    no row that the lookup on the calls keeps names an entry of an array. hSz, hled: the ledger in
    front has its sizes.
  - NOTHING HERE SAYS THAT A FORM IS WORTH 0 AT ANY STATE: the sentence in front is a premise.
  - At "guests" the reader's list of forms is empty: there the sentence is its tests alone. At
    "objects" the forms are the kept rows, none of which names an entry: what is carried is an
    equation on what lies under filled slots, which a later ledger keeps.
  - The stated data are `Stated.of u`: that the mask row is the same at both states is by that
    term's make.
  - Nothing on any property.
-/
import Johnson.Desc.K6.Honest.Law.Keeps
import Johnson.Desc.Kinds.Law.K6ObjectsKept
import Johnson.Desc.Reads.FormsPass

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Honest
open OnBytes.Model (Fork)
open OnBytes.PscRun (Later Sized)
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Desc.First (S HeadOwn ledgerB)
open VerifiableInference.Desc.Kinds.Head.Law (k6Silent)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (ObjectsStates ObjectsBack kept_on readers_kept
  readers_kept_on segAt_head)
open VerifiableInference.Desc.K9 (Readers readersOfLink statesOfLink segAt? formsInT affInT)
open VerifiableInference.Desc.Sound (MsgQ dataQ Rides Stated UFn formsTQ formsTQ_in value_ridesW)
open VerifiableInference.Reads.Pass (Fwd)

/-! ## 1 The general step -/

/-- **From the sentence at the earlier state s to the sentence at the later state s', at one
witness.** CONDITIONAL: ha, hb: both states have their parts; hl: what the reader answers at s it
answers at s'; hon: the public test at s'; hr: the later part rides on the earlier one; hat: the
stated data agree at both states at what the reader's forms name; h: the sentence at s. -/
theorem formsTQ_on (own : List (ℕ × ℕ)) (Rd : Readers) (St : Stated) (piece : ℕ) (run : String)
    (s s' : S) (a b : K9.Part) (rd : ℕ × ℕ → MsgQ) (ha : segAt? s = some a)
    (hb : segAt? s' = some b) (hl : Fwd Rd piece run s s')
    (hon : formsInT Rd own piece run s' = true) (hr : Rides own a b)
    (hat : ∀ R : K9.Read, Rd.forms piece run s = some R → ∀ f ∈ R.forms,
      (∀ x ∈ f.ents.toList, ∀ c : ℕ × String, a.L.arrayOf[x.tree]? = some c →
        (St.at1 s' (dataQ own b rd)).cell c.1 c.2 x.row x.idx =
          (St.at1 s (dataQ own a rd)).cell c.1 c.2 x.row x.idx) ∧
      ∀ x ∈ f.slots.toList,
        (St.at1 s' (dataQ own b rd)).mask x.1 = (St.at1 s (dataQ own a rd)).mask x.1)
    (h : formsTQ Rd St own piece run s rd) : formsTQ Rd St own piece run s' rd := by
  obtain ⟨a', R, ha', hs, _, hf⟩ := h
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  have hs' : Rd.forms piece run s' = some R := hl R hs
  unfold formsInT at hon
  rw [hb, hs'] at hon
  obtain ⟨hlate, hall⟩ := Eq.mp (Bool.and_eq_true _ _) hon
  refine ⟨b, R, hb, hs', hlate, fun f hm => ⟨List.all_eq_true.1 hall f hm, ?_⟩⟩
  have h2 := (hf f hm).1
  unfold affInT at h2
  obtain ⟨_, h3⟩ := Eq.mp (Bool.and_eq_true _ _) h2
  rw [value_ridesW own (K9.mergeOf s) R.late a' b (St.at1 s (dataQ own a' rd))
    (St.at1 s' (dataQ own b rd)) hr.arrays hr.filled f (List.all_eq_true.1 h3)
    (hat R hs f hm).1 (hat R hs f hm).2]
  exact (hf f hm).2

/-! ## 2 The state behind a yes, written out -/

/-- The state behind is the state in front with the head's ledger turned into a later one, and what
the sub-protocol's rounds have heard and the squares' level's state laid. -/
theorem K6Keeps.shape {s s' : S} (K : K6Keeps s s') :
    ∃ (o : HeadOwn) (F1 : Fork) (X : OnBytes.Model.Head.Heard) (Q : OnBytes.Model.Psc),
      s.here = .head o ∧ o.opened = true ∧ Later o.F F1 ∧
        s' = { s with here := .head { o with F := F1, x := some X, squaresP := some Q } } := by
  obtain ⟨o, o', ho, ho', e⟩ := K.own
  have hs := K.here
  obtain ⟨_, _, o1, o1', h1, h1', hop, hx, hq, L, _⟩ := K
  rw [ho] at h1
  rw [ho'] at h1'
  cases h1
  cases h1'
  obtain ⟨X, hX⟩ := Option.isSome_iff_exists.1 hx
  obtain ⟨Q, hQ⟩ := Option.isSome_iff_exists.1 hq
  refine ⟨o, o'.F, X, Q, ho, hop, L, ?_⟩
  have e2 : o' = { o with F := o'.F, x := some X, squaresP := some Q } := by
    rw [← hX, ← hQ]
    exact e
  rw [← e2, ← ho']
  exact hs

/-! ## 3 At the two runs -/

section
variable {Lk : Link S Claim} {b : ℕ} (hS : ObjectsStates (statesOfLink Lk) b)

include hS

/-- **What the segment's reader answers in front it answers behind.** CONDITIONAL: hS, hB: on the
link's list of rounds; the name is one of the two; the chain stands in the opened head's link;
something is heard, and no kept row names an entry. -/
theorem k6_reads_fwd (hB : ObjectsBack (statesOfLink Lk) b) (P8 : K8.ReadsQuiet.PH)
    (small : S → Option K9.Read) (name : String) (hn : name = "objects" ∨ name = "guests") (s : S)
    (o : HeadOwn) (F1 : Fork) (X : OnBytes.Model.Head.Heard) (Q : OnBytes.Model.Psc)
    (ho : s.here = .head o) (hop : o.opened = true) (g : OnBytes.Model.Forest.Heard)
    (hg : s.lookHeard? = some g) (hbare : ∀ f ∈ g.rows.toList, f.ents = #[]) :
    Fwd (readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk) b name s
      { s with here := .head { o with F := F1, x := some X, squaresP := some Q } } := by
  intro R hR
  have hlk : ({ s with here := .head { o with F := F1, x := some X, squaresP := some Q } } :
      S).lookHeard? = s.lookHeard? := by
    unfold S.lookHeard?
    rw [ho]
  have hFb : ({ s with here := .head { o with F := F1, x := some X, squaresP := some Q } } :
      S).fork? = some F1 := by
    show (if o.opened then some F1 else none) = some F1
    rw [hop]
    rfl
  have k0 := readers_kept hS P8 small name hn s R hR
  have kb := readers_kept_on hS hB P8 small name hn _ F1 g hFb (hlk.trans hg) hbare
  rw [kb, hlk]
  exact k0

/-- **The stated data agree at both states at what the reader's forms name.** The end is the text of
the library's `StatedSame`, written out. CONDITIONAL: hS; the name is one of the two; the chain
stands in the opened head's link; no kept row names an entry. -/
theorem k6_stated_at (P8 : K8.ReadsQuiet.PH) (small : S → Option K9.Read) (u : UFn)
    (own : List (ℕ × ℕ)) (name : String) (hn : name = "objects" ∨ name = "guests") (s : S)
    (o : HeadOwn) (F1 : Fork) (X : OnBytes.Model.Head.Heard) (Q : OnBytes.Model.Psc)
    (ho : s.here = .head o) (hop : o.opened = true)
    (hbare : ∀ g, s.lookHeard? = some g → ∀ f ∈ g.rows.toList, f.ents = #[])
    (rd : ℕ × ℕ → MsgQ) :
    ∀ a c, segAt? s = some a →
      segAt? { s with here := .head { o with F := F1, x := some X, squaresP := some Q } } = some c →
      ∀ R : K9.Read, (readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk).forms b name s =
          some R → ∀ f ∈ R.forms,
        (∀ x ∈ f.ents.toList, ∀ t : ℕ × String, a.L.arrayOf[x.tree]? = some t →
          ((Stated.of u).at1
              { s with here := .head { o with F := F1, x := some X, squaresP := some Q } }
              (dataQ own c rd)).cell t.1 t.2 x.row x.idx =
            ((Stated.of u).at1 s (dataQ own a rd)).cell t.1 t.2 x.row x.idx) ∧
        ∀ x ∈ f.slots.toList,
          ((Stated.of u).at1
              { s with here := .head { o with F := F1, x := some X, squaresP := some Q } }
              (dataQ own c rd)).mask x.1 =
            ((Stated.of u).at1 s (dataQ own a rd)).mask x.1 := by
  intro a c ha hc R hR f hf
  have ea := Option.some.inj ((segAt_head s o ho hop).symm.trans ha)
  have ec := Option.some.inj ((segAt_head
    { s with here := .head { o with F := F1, x := some X, squaresP := some Q } }
    { o with F := F1, x := some X, squaresP := some Q } rfl hop).symm.trans hc)
  subst ea
  subst ec
  have k0 := readers_kept hS P8 small name hn s R hR
  refine ⟨fun x hx => ?_, fun _ _ => rfl⟩
  exfalso
  unfold Law.AtTable.keptOf at k0
  rcases hn with rfl | rfl
  · rw [if_pos rfl] at k0
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 k0
    rw [hbare g hg f hf] at hx
    exact nomatch hx
  · rw [if_neg (by decide)] at k0
    rw [← Option.some.inj k0] at hf
    exact nomatch hf

/-- **AT ONE OF THE TWO NAMES THE SENTENCE GOES FORWARD OVER THE TURNING OF THE HEAD'S LEDGER, OF
WHAT IT HAS HEARD AND OF ITS SUMCHECK.** CONDITIONAL: hS, hB: on the link's list of rounds; the name
is one of the two; the chain stands in the opened head's link; the later ledger keeps what is
filled; the ledger in front has its sizes; something is heard, and no kept row names an entry; h:
the sentence in front. -/
theorem kept_fwd (hB : ObjectsBack (statesOfLink Lk) b) (P8 : K8.ReadsQuiet.PH)
    (small : S → Option K9.Read) (u : UFn) (own : List (ℕ × ℕ)) (name : String)
    (hn : name = "objects" ∨ name = "guests") (s : S) (o : HeadOwn) (F1 : Fork)
    (X : OnBytes.Model.Head.Heard) (Q : OnBytes.Model.Psc) (ho : s.here = .head o)
    (hop : o.opened = true) (hL : Later o.F F1) (hSz : Sized o.F)
    (g : OnBytes.Model.Forest.Heard) (hg : s.lookHeard? = some g)
    (hbare : ∀ f ∈ g.rows.toList, f.ents = #[]) (rd : ℕ × ℕ → MsgQ)
    (h : formsTQ (readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk) (Stated.of u) own b name
      s rd) :
    formsTQ (readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk) (Stated.of u) own b name
      { s with here := .head { o with F := F1, x := some X, squaresP := some Q } } rd := by
  have ha := segAt_head s o ho hop
  have hb := segAt_head { s with here := .head { o with F := F1, x := some X, squaresP := some Q } }
    { o with F := F1, x := some X, squaresP := some Q } rfl hop
  have hin := formsTQ_in (Stated.of u) _ own b name s rd h
  refine formsTQ_on own _ _ b name s _ _ _ rd ha hb
    (k6_reads_fwd hS hB P8 small name hn s o F1 X Q ho hop g hg hbare)
    (kept_on hS hB P8 small own name hn s o F1 X Q ho hop hL hSz g hg hbare hin) ?_
    (k6_stated_at hS P8 small u own name hn s o F1 X Q ho hop ?_ rd _ _ ha hb) h
  · exact ⟨rfl, rfl, fun _ _ _ e => e, fun _ e => e, fun _ _ e => e, fun _ _ _ _ => ⟨rfl, rfl⟩,
      fun j _ hj => ⟨(hL.keep j hj).2.1, (hL.keep j hj).2.2⟩⟩
  · intro g' hg'
    obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg')
    exact hbare

/-- **The same at the sub-protocol's own clause on two states and one public test.** CONDITIONAL:
hS, hB; the name is one of the two; K: what a yes leaves of the state; hled: the public test "a
ledger is open and has its sizes", in front; something is heard, and no kept row names an entry; h:
the sentence in front. -/
theorem kept_fwd_keeps (hB : ObjectsBack (statesOfLink Lk) b) (P8 : K8.ReadsQuiet.PH)
    (small : S → Option K9.Read) (u : UFn) (own : List (ℕ × ℕ)) (name : String)
    (hn : name = "objects" ∨ name = "guests") {s s' : S} (K : K6Keeps s s')
    (hled : ledgerB s = true) (g : OnBytes.Model.Forest.Heard) (hg : s.lookHeard? = some g)
    (hbare : ∀ f ∈ g.rows.toList, f.ents = #[]) (rd : ℕ × ℕ → MsgQ)
    (h : formsTQ (readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk) (Stated.of u) own b name
      s rd) :
    formsTQ (readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk) (Stated.of u) own b name s'
      rd := by
  obtain ⟨o, F1, X, Q, ho, hop, hL, rfl⟩ := K.shape
  have hF : s.fork? = some o.F := by simp [S.fork?, ho, hop]
  exact kept_fwd hS hB P8 small u own name hn s o F1 X Q ho hop hL ((Law.sized_iff hF).1 hled) g hg
    hbare rd h

end

end VerifiableInference.Desc.Kinds.Head.Honest

#print axioms VerifiableInference.Desc.Kinds.Head.Honest.formsTQ_on
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.K6Keeps.shape
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.k6_reads_fwd
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.k6_stated_at
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.kept_fwd
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.kept_fwd_keeps
