-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeHead.lean: the honest side of the kind "lookup"
(K3): THE LOOKUP ON THE HEAD'S CALLS: from the inner items of the library's row out to the field
worth of the table of joints at the head's segment, piece 3. A definition of a proposition; theorems
with proofs.

The library lays that field in a layer of its own beneath the lookups' (`worthHead`, `worthK3Head`,
`fillK3Head`, Johnson/Desc/First/Look/K3HeadFill.lean), under three classes on the head's sizes,
policy and request; the key vectors and the riders are read AT THE TOKEN OF THE REPLY THAT THE STATE
HOLDS. Its one filling lays a guard on the witness's cells in front of the arm
(Johnson/Desc/Sound/MgAllAt.lean). On the honest side the field is to be SHOWN: so all that is asked
of a filling is that the arm suffices.

  `HeadSuffices X D Lk adr rq x Mg`   THE PREMISE ON THE FILLING: at each of the three names, at
                     every state and witness: the library's arm gives the field
  `worthHead_els`    the arm does not read its last letter at the three names
  `headSuffices_fill`   A MEMBER: the lookups' layer over the head's layer, over every filling
  `headSuffices_honest` the honest letters keep it
  `table_head`       the site's shape, packing and first slot are the place's as the filling lays it

Limits. The guarded filling is not shown to meet `HeadSuffices` here (an implication with a premise
more follows from the arm at once; the library's three equations are not called).
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeTable
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtBorder
import Johnson.Desc.First.Look.K3HeadFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Exchange
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc.First.Look (Sent P lookAt)
open VerifiableInference.Desc.Kinds.Head (Sizes Policy Request)
open VerifiableInference.Desc.Kinds.Head.Law (HeadAdr headAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles
open ProofFile.Honest.FirstThread (honest)

local notation "FS" => VerifiableInference.Desc.First.S
local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

section
variable [Sizes] [Policy] {Pp Cells Tok : Type}

/-- **THE PREMISE ON THE FILLING: at the head's calls the library's arm gives the field.** -/
def HeadSuffices (X : OnBytes.Model.Verify.Public) (D : Sent) (Lk : K3Letters Cells Tok)
    (adr : HeadAdr) (rq : Pp → Request) (x : PlaceL) (Mg : Meaning Pp (Wit Cells Tok MsgT)) :
    Prop :=
  ∀ r, r = "planes" ∨ r = "keys" ∨ r = "rider" → ∀ (a : Pp × FS) (y : Strs)
    (w : Wit Cells Tok MsgT),
    (letI := rq a.1
     worthHead D Lk adr x X.H.tl r a.2 w False) → Mg.worth (headLink X) 3 r a y w

/-- The arm does not read its last letter at the three names. -/
theorem worthHead_els [Request] (D : Sent) (Lk : K3Letters Cells Tok) (adr : HeadAdr) (x : PlaceL)
    (tl : OnBytes.Model.HTailF2) (r : String) (hr : r = "planes" ∨ r = "keys" ∨ r = "rider")
    (s : FS) (w : Wit Cells Tok MsgT) (e e' : Prop) :
    worthHead D Lk adr x tl r s w e = worthHead D Lk adr x tl r s w e' := by
  unfold worthHead
  rcases hr with rfl | rfl | rfl
  · rw [if_pos rfl, if_pos rfl]
  · rw [if_neg (by decide), if_pos rfl, if_neg (by decide), if_pos rfl]
  · rw [if_neg (by decide), if_neg (by decide), if_pos rfl, if_neg (by decide),
      if_neg (by decide), if_pos rfl]

/-- **A MEMBER: the lookups' layer over the head's layer, over every filling.** CONDITIONAL ON the
place being there. -/
theorem headSuffices_fill (X : OnBytes.Model.Verify.Public) (D : Sent) (Lk : K3Letters Cells Tok)
    (adr : HeadAdr) (rq : Pp → Request) {x : PlaceL} (hx : headAt X = some x)
    (Mg : Meaning Pp (Wit Cells Tok MsgT)) :
    HeadSuffices X D Lk adr rq x (fillK3All X D Lk (fillK3Head X D Lk adr rq Mg)) := by
  intro r hr a y w h
  rw [fillAll_over_head, worth_at_head X D Lk adr rq Mg hx]
  letI := rq a.1
  rw [worthHead_els D Lk adr x X.H.tl r hr a.2 w _ False]
  exact h

/-- The honest letters keep it. -/
theorem headSuffices_honest {X : OnBytes.Model.Verify.Public} {D : Sent} {Lk : K3Letters Cells Tok}
    {adr : HeadAdr} {rq : Pp → Request} {x : PlaceL} {Mg : Meaning Pp (Wit Cells Tok MsgT)}
    (h : HeadSuffices X D Lk adr rq x Mg)
    (ans : Nat → Nat → Pp × FS → Strs → Wit Cells Tok MsgT → Prop)
    (test : Nat → FS → Option String) : HeadSuffices X D Lk adr rq x (honest Mg ans test) := h

end

/-- **At the head's calls.** CONDITIONAL ON the site being one of the public part's, its sort, its
link being the head's, and the place being there. No instance of these hypotheses is exhibited in
this file. -/
theorem table_head (Z : Pub) (s : Site) (hs : s ∈ lookSites Z) (hd : s.digits = false)
    (hl : s.link = headLink Z.p.X) {x : PlaceL} (hx : headAt Z.p.X = some x) :
    s.shape = x.fs ∧ s.p.lm = x.lm ∧ s.p.first = x.F.next := by
  obtain ⟨pl, h1, h2, h3⟩ := site_place Z s hs
  rw [hd, hl] at h1
  rw [hd] at h2
  unfold headAt at hx
  obtain ⟨x', e1, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨h', e3, rfl⟩ := Option.map_eq_some_iff.1 hx
  obtain rfl : pl = x' := Option.some.inj (h1.symm.trans e1)
  rw [h2] at h3
  exact ⟨Option.some.inj (h3.symm.trans e3), by rw [h2]; rfl, by rw [h2]; rfl⟩

#print axioms ProofFile.Honest.K3.Law.Exchange.worthHead_els
#print axioms ProofFile.Honest.K3.Law.Exchange.headSuffices_fill
#print axioms ProofFile.Honest.K3.Law.Exchange.headSuffices_honest
#print axioms ProofFile.Honest.K3.Law.Exchange.table_head

end ProofFile.Honest.K3.Law.Exchange
