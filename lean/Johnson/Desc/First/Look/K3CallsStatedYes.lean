-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place of a stored set is shown at which all premises hold together.
Johnson/Desc/First/Look/K3CallsStatedYes.lean: A YES OF THE SEATED PIECE IS A YES OF THE KIND's OWN
decide: at a piece that holds "below B'", B' any block that narrows the value of K3.theStated at the
address of a link's lookup on the calls. One theorem. A tie of texts: no error term; none of the
table of joints' files lies beneath. NO SOUNDNESS IS CLAIMED.

OBJECT: the value B of K3.theStated claim readers X codes shape a
  (Johnson/Desc/First/Look/K3Stated.lean), and any block B' that narrows it.
USER: k3_att_atTable_stated, k3_lay_atTable_stated (Johnson/Desc/First/Look/K3RowsStated.lean).
LETTERS: a with a.link = some i, a.piece = K3.pieceAt X i false; x: any place whose parameters are
  placeAt X i false's value; W free.

Main name:
  `k3_calls_stated_yes`: where the piece puts c out at s: there are the address's own count of
    padding places and list of what must have been sent, rounds whose words are below the prime,
    and columns, at which K3.block's decide at seatCalls claim says yes at s.1 AND GIVES c.1:
    through the equations of texts (theStated_is, theWhole_is, theOwn_is: K3OwnIs.lean), the rules
    on narrower and on joined blocks (out_narrow, below_thenQuiet_narrows, out_thenQuiet),
    quiet_calls_same and blockVia_decide.

Limits. At the piece, not at decide: at a layers' link the seated block is a joined one (the lookup,
then a step without a round): its decide is shown a cut of the rounds. hOk, hN, hp, hback are
premises.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsStated

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

section
variable {Cl W : Type} {Fr : Frame} {X : Verify.Public} {i : ℕ} {x : Desc.First.Look.Place}

local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- **A yes of the seated piece is a yes of the kind's own decide.** -/
theorem k3_calls_stated_yes (claim : Aff → Cl) (readers : ℕ → Option (Desc.K3.Readers Desc.First.S))
    (codes : Codes) (shape : Params.ReqShape) (a : Desc.Place)
    (B B' : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (hN : B'.Narrows B)
    (p : Piece (ckP .two) Fr Desc.First.S Cl W) (hp : p.b = below B')
    (hl : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i false)
    (e : placeAt X i false = some theP) (hback : p.back = [])
    (s c : Desc.First.S × Fr.E.Str) (τ : Tr (uLT (ckP .two) p.ds))
    (hc : p.ior.red.out s τ = some c) :
    ∃ (laid : Array Nat) (sent : List (ℕ × ℕ)) (rs : List Fmt.RoundView)
      (cols : List (List (ℕ × List UInt64))), okRoundsE rs = true ∧
      (Desc.K3.block (Desc.K3.seatCalls claim) a.piece laid sent theP []).decide s.1 rs cols =
        .ok c.1 := by
  obtain ⟨B₁, hB₁, e1, e2, -, e4⟩ := Desc.K3.theStated_is claim readers X codes shape a B h
  obtain ⟨b, hb, hW⟩ := Desc.K3.theWhole_is claim true X codes shape a B₁ hB₁
  obtain ⟨j, digits, P, sent, laid, hj, hpj, hP, -, -, r1, r2, -, r4⟩ :=
    Desc.K3.theOwn_is claim true X codes shape a b hb
  obtain rfl : i = j := Option.some.inj (hl.symm.trans hj)
  cases digits with
  | true => exact absurd (hpj.symm.trans hpc) (pieceAt_ne X i)
  | false =>
    have eP : P = theP := Option.some.inj (hP.symm.trans e)
    subst eP
    have sV : (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP []).Same b :=
      ⟨r1.symm, r2.symm⟩
    have sB : B₁.Same B := ⟨e1.symm, e2.symm⟩
    -- the piece at the maker's own block puts out the same
    have key : b.planOk = true ∧
        ({ p with b := below (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
          []) } : Piece (ckP .two) Fr Desc.First.S Cl W).ior.red.out s τ = some c := by
      rcases hW with ⟨-, rfl⟩ | ⟨f, hf, rfl⟩
      · refine ⟨e4.symm.trans hOk, ?_⟩
        refine out_narrow
          ({ p with b := below (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent
            theP []) } : Piece (ckP .two) Fr Desc.First.S Cl W) p.b ?_ s c τ hc
        rw [hp]
        exact (hN.trans (sV.trans sB).symm.narrows).below
      · have hpl : (b.andThen b.name
            (Desc.roundlessBlock (b.name ++ ": behind it") 1 a.link a.piece f)).planOk = true :=
          e4.symm.trans hOk
        have h1 : ({ p with b := ((below (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
            laid sent theP [])).andThen b.name
              (Desc.roundlessBlock (b.name ++ ": behind it") 1 a.link a.piece f)) } :
            Piece (ckP .two) Fr Desc.First.S Cl W).ior.red.out s τ = some c := by
          refine out_narrow ({ p with b := ((below (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim)
            a.piece laid sent theP [])).andThen b.name
              (Desc.roundlessBlock (b.name ++ ": behind it") 1 a.link a.piece f)) } :
            Piece (ckP .two) Fr Desc.First.S Cl W) p.b ?_ s c τ hc
          rw [hp]
          exact ((hN.trans ((sV.andThen (Desc.Block.Same.refl _) b.name b.name).trans
            sB).symm.narrows).below).trans (below_thenQuiet_narrows _ _ _ _ _ _ _)
        obtain ⟨s', h2, h3⟩ := out_thenQuiet
          ({ p with b := below (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent
            theP []) } : Piece (ckP .two) Fr Desc.First.S Cl W) _ _ _ _ _ f s c τ h1
        have e5 : c.1 = s' := quiet_calls_same X a i hl hpc f hf s' c.1 h3
        refine ⟨?_, ?_⟩
        · have h6 : (b.planOk && (Desc.roundlessBlock (b.name ++ ": behind it") 1 a.link a.piece
              f).planOk) = true := hpl
          exact (Eq.mp (Bool.and_eq_true _ _) h6).1
        · rw [h2, ← e5]
    obtain ⟨hbk, hout⟩ := key
    obtain ⟨-, -, hw, cols, hd⟩ := piece_hears_below
      ({ p with b := below (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
        []) } : Piece (ckP .two) Fr Desc.First.S Cl W) _ rfl hback s τ c hout
    exact ⟨laid, sent, _, cols, hw, Desc.K3.Law.blockVia_decide (r4 hbk) hd⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_calls_stated_yes
