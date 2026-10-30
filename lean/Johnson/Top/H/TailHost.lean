-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/TailHost.lean: the seam from the sending of the reads into the draw of the matrix of a
smallness test, with its premise paid, at the letters of a sub-proof's frame.

Johnson/Top/H/TailSeams.lean leaves one premise at that seam (`hrel`): the joint before the draw
gives the joint before the sending, a part of whose witness is read off the sent messages. A frame
(`Cb.Pv.Tail.Host`, Cb/Pv/Tail/InLink.lean) has: a base joint B₀ in front of the sending; a ledger
of the verifier's linear claims on early and late entries; the late entries, which are the reads.
In front of the sending stands `Cb.Sub.virtJ B₀ a msg₁ n` (Cb/Sub/LateJoin.lean): B₀, and the ledger
pulled back to the early entries holds. Before the draw stands the block's joint at the letters
`Host.let`: B₀, the ledger on early and late entries, and there are cells. That the second gives the
first is `Cb.Pv.Tail.host_seam` with `Cb.Sub.late_holds`. Definitions, statements and proofs.

Main names:
  `tailHost`: the frame's letters, where the messages are those of a signature S₁ and of the family
    that is sent.
  `tailSentOf`: the record `SentCaller` of Johnson/Top/H/TailSeams.lean at these letters;
    `tailSentOf_letters`: its caller's letters are `Host.let`, by definition.
  `tailHost_hrel`: the premise, under the three inequalities `Size.Uniq` at the field's
    characteristic and three laws on the frame's letters: the early entry at the place of a cell is
    the cell behind the committed symbols (`hc`); the form of a late entry is the form of its read
    on the cells' places (`ha`); a late entry is the committed read at its place (`ht`).
  `tailHost_into_ok`, `tailHost_cf_ok`: so the seam holds, between joints with their conditions
    (behind `kSendInto`) and between joints whose condition may fail (behind `kSend`).

Limits: the three laws are hypotheses: they are shown of no sub-proof here. Those of
Cb/Pv/Tail/InLink.lean and Johnson/Top/H/TailSeams.lean.
-/
import Johnson.Top.H.TailSeamsInto
import Cb.Pv.Tail.InLink
import Cb.Sub.LateJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob Hiop Cb IOR TWhole VerifiableInference.OnPublicFiles Cb.Sub Cb.Pv.Tail

section
variable {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] {s : Size} {K Xe Wp Wp₁ : Type} {Ex : ExtSpec}
  (S₁ : Sig Cb.Gl.E) (snd : Cb.Pv.Send.Size Cb.Gl.E) (bk₁ : snd.N.Msg → Wp₁ → Wp)
  (B₀ : Rels K Xe Ex (S₁.Msg × Wp)) (msg₁ : S₁.Msg → J₁ → Cb.Gl.E)
  (ent : snd.N.Msg → J₂ → Cb.Gl.E)
  (w : Xe → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.m μ) → Cb.Gl.E)
  (sym : S₁.Msg → Syms Cb.Gl.E s)
  (tab : snd.N.Msg → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.k μ) → Cb.Gl.E)
  (dig : Wp₁ → Dig Cb.Gl.E s)

/-- The frame's letters over a signature and the family that is sent. -/
@[reducible] def tailHost : Host Cb.Gl.E s J₁ J₂ where
  Xe := Xe
  Ex := Ex
  M := (S₁.sum snd.N).Msg
  M₁ := S₁.Msg
  U₁ := snd.N.Msg
  left := S₁.left snd.N (T := OMsg.Msg)
  right := S₁.right snd.N (T := OMsg.Msg)
  Wp := Wp
  Wp₁ := Wp₁
  Kc := K
  bk₁ := bk₁
  B₀ := B₀
  msg₁ := msg₁
  ent := ent
  w := w
  sym := sym
  tab := tab
  dig := dig

local notation "Qh" => tailHost S₁ snd bk₁ B₀ msg₁ ent w sym tab dig

/-- Who calls the draw behind the sending of the reads. -/
@[reducible] def tailSentOf : SentCaller :=
  ⟨S₁, snd, s, (Qh).let.X, Ex, Wp₁, (Qh).let.w, (Qh).let.sym, (Qh).let.tab, (Qh).let.dig,
    (Qh).let.ride⟩

local notation "Dh" => tailSentOf S₁ snd bk₁ B₀ msg₁ ent w sym tab dig

theorem tailSentOf_letters : (Dh).caller.letters = (Qh).let := rfl

/-- The seam's premise, paid. -/
theorem tailHost_hrel (p : ℕ) [CharP Cb.Gl.E p] (hu : s.Uniq p) (a : Xe → J₂ → Aff Cb.Gl.E J₁)
    (ic : JCell s → J₁) (it : J₂ → JTab s)
    (hc : ∀ m₁ j, msg₁ m₁ (ic j) = cellValS (sym m₁) j)
    (ha : ∀ (x : (Qh).let.X) j v,
      (a x.1 j).val v = (affRead (Qh).let x (it j)).val fun i => v (ic i))
    (ht : ∀ u j, ent u j = tab u (it j).1 (it j).2.1 (it j).2.2) (n : ℕ) :
    ∀ b v, (virtJ B₀ a msg₁ n).on b → (Cb.Pv.Tail.A (Dh).caller.letters).relR b v →
      (S₁.grow snd.N (virtJ B₀ a msg₁ n) bk₁).relR b v := by
  intro b v _ h
  obtain ⟨h1, h2, h3⟩ := host_seam (Qh) p hu a ic it hc ha ht
    (fun z => B₀.core (S₁.left snd.N (T := OMsg.Msg) z.1,
      bk₁ (S₁.right snd.N (T := OMsg.Msg) z.1) z.2)) b v.1 v.2 h
  exact ⟨h1, (late_holds _ _ _ _ h2).1 h3⟩

/-- The seam behind a sending that ends at a joint with its condition. -/
theorem tailHost_into_ok (p : ℕ) [CharP Cb.Gl.E p] (hu : s.Uniq p)
    (a : Xe → J₂ → Aff Cb.Gl.E J₁) (ic : JCell s → J₁) (it : J₂ → JTab s)
    (hc : ∀ m₁ j, msg₁ m₁ (ic j) = cellValS (sym m₁) j)
    (ha : ∀ (x : (Qh).let.X) j v,
      (a x.1 j).val v = (affRead (Qh).let x (it j)).val fun i => v (ic i))
    (ht : ∀ u j, ent u j = tab u (it j).1 (it j).2.1 (it j).2.2) (n : ℕ) :
    (tailIntoRng (Dh) (virtJ B₀ a msg₁ n) bk₁).OK :=
  tailIntoRng_ok _ _ _ (tailHost_hrel S₁ snd bk₁ B₀ msg₁ ent w sym tab dig p hu a ic it hc ha ht n)

/-- The seam behind a sending that ends at a joint whose condition may fail. -/
theorem tailHost_cf_ok (p : ℕ) [CharP Cb.Gl.E p] (hu : s.Uniq p)
    (a : Xe → J₂ → Aff Cb.Gl.E J₁) (ic : JCell s → J₁) (it : J₂ → JTab s)
    (hc : ∀ m₁ j, msg₁ m₁ (ic j) = cellValS (sym m₁) j)
    (ha : ∀ (x : (Qh).let.X) j v,
      (a x.1 j).val v = (affRead (Qh).let x (it j)).val fun i => v (ic i))
    (ht : ∀ u j, ent u j = tab u (it j).1 (it j).2.1 (it j).2.2) (n : ℕ) :
    (seamToRng (Dh) (virtJ B₀ a msg₁ n) bk₁).OK :=
  seamToRng_ok _ _ _ (tailHost_hrel S₁ snd bk₁ B₀ msg₁ ent w sym tab dig p hu a ic it hc ha ht n)

end

end KObj

#print axioms KObj.tailHost_hrel
#print axioms KObj.tailHost_into_ok
#print axioms KObj.tailHost_cf_ok
