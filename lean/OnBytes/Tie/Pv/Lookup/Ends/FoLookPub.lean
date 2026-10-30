-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLookPub.lean.
A lookup's share of a sub-proof's public record, and what is asked of it.

A link of a chain of sub-proofs is made of a public record. For each of its two lookups that record
holds four things: the lookup's record of public numbers, the type of the entries that the lookup
reads, the layout (where the keys, the bits of the counts and the mask row lie), and how the entries
are read off the committed messages. This file has these four as one structure over a base reading
M₀, so that a value written once is pulled back along any door's reading of its messages; and the
clauses that the statements on the lookup ask of them, at the arguments with which the byte-level
verifier calls Forest.pad.

Main names:
  `LookPub M₀ St`: h, J₀ (finite, with decidable equality), L, rd₀. `LookPub.msg`: the entries read
    off messages of any type, along a reading rd of these in M₀.
  `LookPubOK p calls pub lid lm next mk pl`: ShapeOf at p.h; 5 ≤ lm ≤ p.h.kT + 5; the layout's mask
    entries are mk from next on; the layout's cells are pl at the planes' matrix of 2^lm rows.
  `LookPubOK.ok`: FoNums.ok p.h = true.
  `LookPubOK.outAt`: whatever the typed verifier puts out at a typed transcript τ is the
    out-statement that the plain data of τ describe (Fo.OutAt): a law for every τ, not a field.
  `LookPubOK.hOut`: for claims Dn and Todo on the out-statement and the messages: if Dn gives, at
    some plain data with Fo.OutAt (at the out-statement's own state x.1.1), the claims that ride
    (Fo.Dnl.DnL), and Todo then the claim on the keys (Fo.Dnl.JoinIs), then Dn and Todo give the
    lookup's out-claim at the entries read along rd. The «some» stands in the premise.
No caller occurs here.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoDnl
import OnBytes.Tie.Pv.Lookup.Peel.FoPayCaller

set_option autoImplicit false

namespace Fo.Pub2
open Iop IOR Cb Cb.Tw Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwV Tw3 Tw Cb.Fo Cb.Fo.NumsEq Cb.Fo.Pin
open Cb.Fo.PlaneClaims OnBytes OnBytes.Model Fo.Dnl

/-- A lookup's share of a public record, over a base reading M₀. -/
structure LookPub (M₀ St : Type) : Type 1 where
  /-- the lookup's record of public numbers -/
  h : Forest.Shape
  /-- the entries of the committed messages that the lookup reads -/
  J₀ : Type
  [finJ : Fintype J₀]
  [decJ : DecidableEq J₀]
  /-- where the keys, the bits of the counts and the mask row lie -/
  L : Lay Cb.Gl.E St J₀
  /-- the entries, read off the base reading -/
  rd₀ : M₀ → J₀ → Cb.Gl.E

attribute [instance] LookPub.finJ LookPub.decJ

variable {M₀ St : Type}

/-- The entries read off messages of any type, along a reading of these in M₀. -/
def LookPub.msg (p : LookPub M₀ St) {M : Type} (rd : M → M₀) : M → p.J₀ → Cb.Gl.E :=
  fun m => p.rd₀ (rd m)

/-- What is asked of the record, at the arguments with which the run calls Forest.pad. -/
structure LookPubOK (p : LookPub M₀ St) (calls : Array Call) (pub : Array ℕ) (lid lm next : ℕ)
    (mk : ℕ → p.J₀) (pl : ℕ → ℕ → p.J₀) : Prop where
  shape : ShapeOf calls pub lid p.h
  lm5 : 5 ≤ lm
  lmT : lm ≤ p.h.kT + 5
  masks : ∀ s, p.L.mkS s = mk (next + s)
  cells : ∀ t k j, k < p.h.NC →
    p.L.bc t k j = pl (FoNums.cellRC p.h lm (t, k, j)).1 (FoNums.cellRC p.h lm (t, k, j)).2

variable {p : LookPub M₀ St} {calls : Array Call} {pub : Array ℕ} {lid lm next : ℕ}
  {mk : ℕ → p.J₀} {pl : ℕ → ℕ → p.J₀}

theorem LookPubOK.ok (k : LookPubOK p calls pub lid lm next mk pl) : FoNums.ok p.h = true :=
  Fo.Pay.shapeOf_ok k.shape

/-- What the typed verifier puts out is what the plain data of the transcript describe. -/
theorem LookPubOK.outAt (k : LookPubOK p calls pub lid lm next mk pl) (Ex : ExtSpec)
    (a : St × Ex.Str) (τ : Tr (forB Cb.Gl.E p.h p.L V₀ V₀C (Ex := Ex)).R.shape)
    (b : TX (St × Cb.Gl.E) Cb.Gl.E (Option p.J₀) × Ex.Str)
    (hb : (forB Cb.Gl.E p.h p.L V₀ V₀C (Ex := Ex)).R.red.out a τ = some b) :
    OutAt p.h lm next (placeOf mk pl) (forFl p.h p.L Ex τ) a.1 b.1 ∧ b.2 = a.2 :=
  outAt_run p.h k.ok p.L lm next mk pl k.masks k.cells Ex a τ b hb

/-- In the shape of the clause hOut of a link's public record. -/
theorem LookPubOK.hOut (k : LookPubOK p calls pub lid lm next mk pl) {M : Type} (rd : M → M₀)
    (Dn Todo : TX (St × Cb.Gl.E) Cb.Gl.E (Option p.J₀) → M → Prop)
    (hDn : ∀ x m, Dn x m → ∃ rs : Rounds Cb.Gl.E,
      OutAt p.h lm next (placeOf mk pl) rs x.1.1 x ∧ DnL p.h lm next mk pl rs (p.msg rd m) ∧
        (Todo x m → JoinIs p.h p.L lm next mk pl rs x.1.1 (p.msg rd m))) :
    ∀ x m, Dn x m → Todo x m → (forA Cb.Gl.E p.h p.L).lk.out id id x (zext (p.msg rd m)) := by
  intro x m hd ht
  obtain ⟨rs, hx, D, hJ⟩ := hDn x m hd
  exact dnl_out k.ok k.lm5 k.lmT hx D (hJ ht)

end Fo.Pub2
