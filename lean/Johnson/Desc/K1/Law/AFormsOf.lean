-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/AFormsOf.lean: THE CALL aForms_of: the
arm aForms of hgo_of_arms (K1/Law/GoAtLater.lean) at one later place of kind K1: the riding
item forms m j r goes back over the block's own yes, from inside the promise in front. A statement
with its proof: a call of go_forms_later (K1/Law/GoAtLaterForms.lean). The letter
after has its type by segment.

OBJECT. Any block B over the chain's state with LaterSend P B, LaterGrows B and two declared rounds
(members: laterAt, IM.k1Reads). USER. aForms at N := D.N, links := linksFull,
ps := flatPlacesOf linksFull true, k := noL l d, P := parL Z G l d, B := blkL Z G l d X arrs,
base := (L l d).1. LETTERS. D, base0, arr, ms, St, after, wt, rwB, Mg0, Mg.
PAID INSIDE: the tied public item formsIn m j r in front (formsIn_open; inAt_pub) · the clause on
the book (inAt_book) · two rounds off the fit of YesOf.
PREMISES THAT STAY, BY NAME.
  hpub · hforms   two equations on Mg (at the composed meaning: mgAll_pub, mgAll_forms: rfl).
  hl      ON THE LETTER D.Rd: the reader gives one answer in front and behind, at the runs of an
          item that is open in front.
  hwt     ON THE LETTER wt, at an open item of the name "weights" alone.
  hmeet   AheadMeets (THE CROSSING), at a run that D.ah marks alone.
By a look at the table forms rides at the digits' places alone.
What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.GoAtLaterForms
import Johnson.Desc.K1.Law.PubAtLaterCall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning PubData pubAll)
open VerifiableInference.Desc.K13.Law (openAt)
open VerifiableInference.Desc.Sound (Stated)

variable {Pp Cells Tok : Type}

/-- The public item that is tied to an open item forms m j r is asked in front. -/
theorem formsIn_open (Q : List Pub) (O : List Item) (m j : ℕ) (r : String)
    (h : Item.forms m j r ∈ O) : Pub.formsIn m j r ∈ Q ++ First.pubOfItems O := by
  refine List.mem_append_right _ ?_
  unfold First.pubOfItems
  exact List.mem_flatMap.2 ⟨_, h, List.mem_singleton.2 rfl⟩

/-- **THE CALL aForms_of**: the top's binder aForms at one later place. -/
theorem aForms_of (D : PubData) (base0 : Pub → Pp × S → Bool) (arr : ℕ → ℕ → ℕ)
    (ms : List Sound.Mem) (St : Stated) (after : ℕ → S → Except String S)
    (wt : ℕ → Pp × S → Strs → Wit Cells Tok Sound.MsgT → Prop) (rwB : ℕ → S → Bool)
    (Mg0 Mg : Meaning Pp (Wit Cells Tok Sound.MsgT)) (hpub : Mg.pub = pubAll D base0)
    (hforms : Mg.forms =
      (Sound.meaningForms D.cs arr ms D.Rd D.runs St after D.N wt rwB D.ah Mg0).forms)
    (links : List ModelPart) (ps : List Place) (k : ℕ) (P : Par) (B : Block S Unit)
    (hS : LaterSend P B) (hG : LaterGrows B) (h2 : B.rounds.length = 2) (base : ℕ)
    (hl : ∀ x x' y m j r, YesOf B x x' → InAt D.N Mg links ps k x y →
      Item.forms m j r ∈ openAt links ps k →
      ∀ p ∈ D.runs m j r, (D.Rd m).forms p.1 p.2 x'.2 = (D.Rd m).forms p.1 p.2 x.2)
    (hwt : ∀ x x' y y' w m j, YesOf B x x' → InAt D.N Mg links ps k x y → KeptBelow base y y' →
      Item.forms m j "weights" ∈ openAt links ps k → wt m x' y' w → wt m x y w)
    (hmeet : ∀ x x' y m j r, YesOf B x x' → InAt D.N Mg links ps k x y →
      Item.forms m j r ∈ openAt links ps k → ∀ p ∈ D.runs m j r, D.ah p.1 p.2 = true →
      AheadMeets (D.N.sent m) (D.N.group m) (idsOf P x.2.st.oracles.size).toList x.2 x'.2) :
    ∀ (x x' : Pp × S) y y' w m j r, YesOf B x x' → InAt D.N Mg links ps k x y →
      KeptBelow base y y' → Item.forms m j r ∈ openAt links ps k → Mg.forms m j r x' y' w →
      Mg.forms m j r x y w := by
  intro x x' y y' w m j r hy hIn hk ho h0
  have hin := inAt_pub hIn _ (formsIn_open _ _ m j r ho)
  obtain ⟨hb, _⟩ := inAt_book hIn
  have hy' := hy
  obtain ⟨_, rs, gs, hfit, hd⟩ := hy'
  have hlen : (rs.map noDigest).length = 2 := by
    rw [List.length_map, Keeps.fit_length _ _ hfit, h2]
  rw [hpub] at hin
  rw [hforms] at h0 ⊢
  exact go_forms_later hS hG D arr ms St after wt rwB Mg0 base0 x x' _ gs hlen hd hb m j r
    (hl x x' y m j r hy hIn ho) y y' w
    (fun e => hwt x x' y y' w m j hy hIn hk (by rw [← e]; exact ho)) hin
    (hmeet x x' y m j r hy hIn ho) h0

end VerifiableInference.Desc.K1
