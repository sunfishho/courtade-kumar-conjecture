import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantCheckerSound
import InformationTheory.CourtadeKumar.LRDeterminantRestrictedFiniteRegionCompression
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData000
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData001
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData002
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData003
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData004
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData005
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData006
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData007
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData008
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData009
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData010
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData011
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData012
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData013
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData014
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData015
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData016
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData017
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData018
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData019
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData020
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData021
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData022
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData023
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData024
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData025
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData026
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData027
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData028
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData029
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData030
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData031
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData032
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData033
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData034
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData035
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData036
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData037
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData038
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData039
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData040
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData041
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData042
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData043
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData044
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData045
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData046
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData047
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData048
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData049
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData050
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData051
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData052
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData053
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData054
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData055
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData056
import InformationTheory.CourtadeKumar.AnalyticExtension.DeterminantData057

/-! Complete finite determinant from bounded kernel-checked batches.
The explicit split proofs cover the two closed root boxes. -/
namespace CourtadeKumar.LRDeterminantReducedCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def tinyRoot : CertificateBox := ⟨(1 / 16384), (1 / 128), 1, 4, 0, 1⟩

theorem tiny (p : CertificatePoint) (hp : tinyRoot.Contains p)
    (hi : LRHighShapeInterior p) (hr : LRHighShapeVRelevant p) :
    LRDeterminantClearedSingularAt p := by
  rcases CertificateBox.contains_lower_or_upper hp .chi (1 / 2) with hL0 | hU0
  · rcases CertificateBox.contains_lower_or_upper hL0 .chi (1 / 4) with hL1 | hU1
    · rcases CertificateBox.contains_lower_or_upper hL1 .chi (1 / 8) with hL2 | hU2
      · exact box_sound Batch000.root Batch000.certificate Batch000.checked p hL2 hi hr
      · exact box_sound Batch001.root Batch001.certificate Batch001.checked p hU2 hi hr
    · exact box_sound Batch002.root Batch002.certificate Batch002.checked p hU1 hi hr
  · exact box_sound Batch003.root Batch003.certificate Batch003.checked p hU0 hi hr

def mainRoot : CertificateBox := ⟨(1 / 128), (1 / 10), (1 / 128), 4, 0, 1⟩

theorem main (p : CertificatePoint) (hp : mainRoot.Contains p)
    (hi : LRHighShapeInterior p) (hr : LRHighShapeVRelevant p) :
    LRDeterminantClearedSingularAt p := by
  rcases CertificateBox.contains_lower_or_upper hp .k (513 / 256) with hL3 | hU3
  · rcases CertificateBox.contains_lower_or_upper hL3 .k (515 / 512) with hL4 | hU4
    · rcases CertificateBox.contains_lower_or_upper hL4 .chi (1 / 2) with hL5 | hU5
      · rcases CertificateBox.contains_lower_or_upper hL5 .k (519 / 1024) with hL6 | hU6
        · exact box_sound Batch004.root Batch004.certificate Batch004.checked p hL6 hi hr
        · rcases CertificateBox.contains_lower_or_upper hU6 .s (69 / 1280) with hL7 | hU7
          · exact box_sound Batch005.root Batch005.certificate Batch005.checked p hL7 hi hr
          · exact box_sound Batch006.root Batch006.certificate Batch006.checked p hU7 hi hr
      · exact box_sound Batch007.root Batch007.certificate Batch007.checked p hU5 hi hr
    · rcases CertificateBox.contains_lower_or_upper hU4 .chi (1 / 2) with hL8 | hU8
      · rcases CertificateBox.contains_lower_or_upper hL8 .chi (1 / 4) with hL9 | hU9
        · rcases CertificateBox.contains_lower_or_upper hL9 .chi (1 / 8) with hL10 | hU10
          · exact box_sound Batch008.root Batch008.certificate Batch008.checked p hL10 hi hr
          · rcases CertificateBox.contains_lower_or_upper hU10 .s (69 / 1280) with hL11 | hU11
            · exact box_sound Batch009.root Batch009.certificate Batch009.checked p hL11 hi hr
            · rcases CertificateBox.contains_lower_or_upper hU11 .chi (3 / 16) with hL12 | hU12
              · exact box_sound Batch010.root Batch010.certificate Batch010.checked p hL12 hi hr
              · exact box_sound Batch011.root Batch011.certificate Batch011.checked p hU12 hi hr
        · rcases CertificateBox.contains_lower_or_upper hU9 .s (69 / 1280) with hL13 | hU13
          · exact box_sound Batch012.root Batch012.certificate Batch012.checked p hL13 hi hr
          · exact box_sound Batch013.root Batch013.certificate Batch013.checked p hU13 hi hr
      · exact box_sound Batch014.root Batch014.certificate Batch014.checked p hU8 hi hr
  · rcases CertificateBox.contains_lower_or_upper hU3 .chi (1 / 2) with hL14 | hU14
    · rcases CertificateBox.contains_lower_or_upper hL14 .chi (1 / 4) with hL15 | hU15
      · rcases CertificateBox.contains_lower_or_upper hL15 .s (69 / 1280) with hL16 | hU16
        · rcases CertificateBox.contains_lower_or_upper hL16 .chi (1 / 8) with hL17 | hU17
          · exact box_sound Batch015.root Batch015.certificate Batch015.checked p hL17 hi hr
          · exact box_sound Batch016.root Batch016.certificate Batch016.checked p hU17 hi hr
        · rcases CertificateBox.contains_lower_or_upper hU16 .chi (1 / 8) with hL18 | hU18
          · rcases CertificateBox.contains_lower_or_upper hL18 .k (1537 / 512) with hL19 | hU19
            · rcases CertificateBox.contains_lower_or_upper hL19 .chi (1 / 16) with hL20 | hU20
              · exact box_sound Batch017.root Batch017.certificate Batch017.checked p hL20 hi hr
              · rcases CertificateBox.contains_lower_or_upper hU20 .s (197 / 2560) with hL21 | hU21
                · exact box_sound Batch018.root Batch018.certificate Batch018.checked p hL21 hi hr
                · rcases CertificateBox.contains_lower_or_upper hU21 .k (2563 / 1024) with hL22 | hU22
                  · exact box_sound Batch019.root Batch019.certificate Batch019.checked p hL22 hi hr
                  · exact box_sound Batch020.root Batch020.certificate Batch020.checked p hU22 hi hr
            · rcases CertificateBox.contains_lower_or_upper hU19 .chi (1 / 16) with hL23 | hU23
              · exact box_sound Batch021.root Batch021.certificate Batch021.checked p hL23 hi hr
              · rcases CertificateBox.contains_lower_or_upper hU23 .k (3585 / 1024) with hL24 | hU24
                · rcases CertificateBox.contains_lower_or_upper hL24 .s (197 / 2560) with hL25 | hU25
                  · exact box_sound Batch022.root Batch022.certificate Batch022.checked p hL25 hi hr
                  · rcases CertificateBox.contains_lower_or_upper hU25 .k (6659 / 2048) with hL26 | hU26
                    · exact box_sound Batch023.root Batch023.certificate Batch023.checked p hL26 hi hr
                    · exact box_sound Batch024.root Batch024.certificate Batch024.checked p hU26 hi hr
                · rcases CertificateBox.contains_lower_or_upper hU24 .s (197 / 2560) with hL27 | hU27
                  · exact box_sound Batch025.root Batch025.certificate Batch025.checked p hL27 hi hr
                  · rcases CertificateBox.contains_lower_or_upper hU27 .chi (3 / 32) with hL28 | hU28
                    · rcases CertificateBox.contains_lower_or_upper hL28 .k (7681 / 2048) with hL29 | hU29
                      · exact box_sound Batch026.root Batch026.certificate Batch026.checked p hL29 hi hr
                      · exact box_sound Batch027.root Batch027.certificate Batch027.checked p hU29 hi hr
                    · rcases CertificateBox.contains_lower_or_upper hU28 .k (7681 / 2048) with hL30 | hU30
                      · rcases CertificateBox.contains_lower_or_upper hL30 .s (453 / 5120) with hL31 | hU31
                        · exact box_sound Batch028.root Batch028.certificate Batch028.checked p hL31 hi hr
                        · exact box_sound Batch029.root Batch029.certificate Batch029.checked p hU31 hi hr
                      · rcases CertificateBox.contains_lower_or_upper hU30 .s (453 / 5120) with hL32 | hU32
                        · exact box_sound Batch030.root Batch030.certificate Batch030.checked p hL32 hi hr
                        · rcases CertificateBox.contains_lower_or_upper hU32 .chi (7 / 64) with hL33 | hU33
                          · exact box_sound Batch031.root Batch031.certificate Batch031.checked p hL33 hi hr
                          · rcases CertificateBox.contains_lower_or_upper hU33 .k (15873 / 4096) with hL34 | hU34
                            · exact box_sound Batch032.root Batch032.certificate Batch032.checked p hL34 hi hr
                            · exact box_sound Batch033.root Batch033.certificate Batch033.checked p hU34 hi hr
          · rcases CertificateBox.contains_lower_or_upper hU18 .k (1537 / 512) with hL35 | hU35
            · rcases CertificateBox.contains_lower_or_upper hL35 .s (197 / 2560) with hL36 | hU36
              · exact box_sound Batch034.root Batch034.certificate Batch034.checked p hL36 hi hr
              · rcases CertificateBox.contains_lower_or_upper hU36 .k (2563 / 1024) with hL37 | hU37
                · rcases CertificateBox.contains_lower_or_upper hL37 .chi (3 / 16) with hL38 | hU38
                  · exact box_sound Batch035.root Batch035.certificate Batch035.checked p hL38 hi hr
                  · exact box_sound Batch036.root Batch036.certificate Batch036.checked p hU38 hi hr
                · rcases CertificateBox.contains_lower_or_upper hU37 .chi (3 / 16) with hL39 | hU39
                  · rcases CertificateBox.contains_lower_or_upper hL39 .k (5637 / 2048) with hL40 | hU40
                    · exact box_sound Batch037.root Batch037.certificate Batch037.checked p hL40 hi hr
                    · exact box_sound Batch038.root Batch038.certificate Batch038.checked p hU40 hi hr
                  · exact box_sound Batch039.root Batch039.certificate Batch039.checked p hU39 hi hr
            · rcases CertificateBox.contains_lower_or_upper hU35 .s (197 / 2560) with hL41 | hU41
              · exact box_sound Batch040.root Batch040.certificate Batch040.checked p hL41 hi hr
              · rcases CertificateBox.contains_lower_or_upper hU41 .k (3585 / 1024) with hL42 | hU42
                · rcases CertificateBox.contains_lower_or_upper hL42 .chi (3 / 16) with hL43 | hU43
                  · rcases CertificateBox.contains_lower_or_upper hL43 .k (6659 / 2048) with hL44 | hU44
                    · exact box_sound Batch041.root Batch041.certificate Batch041.checked p hL44 hi hr
                    · rcases CertificateBox.contains_lower_or_upper hU44 .chi (5 / 32) with hL45 | hU45
                      · exact box_sound Batch042.root Batch042.certificate Batch042.checked p hL45 hi hr
                      · exact box_sound Batch043.root Batch043.certificate Batch043.checked p hU45 hi hr
                  · exact box_sound Batch044.root Batch044.certificate Batch044.checked p hU43 hi hr
                · rcases CertificateBox.contains_lower_or_upper hU42 .chi (3 / 16) with hL46 | hU46
                  · rcases CertificateBox.contains_lower_or_upper hL46 .k (7681 / 2048) with hL47 | hU47
                    · rcases CertificateBox.contains_lower_or_upper hL47 .chi (5 / 32) with hL48 | hU48
                      · exact box_sound Batch045.root Batch045.certificate Batch045.checked p hL48 hi hr
                      · exact box_sound Batch046.root Batch046.certificate Batch046.checked p hU48 hi hr
                    · rcases CertificateBox.contains_lower_or_upper hU47 .chi (5 / 32) with hL49 | hU49
                      · rcases CertificateBox.contains_lower_or_upper hL49 .s (453 / 5120) with hL50 | hU50
                        · exact box_sound Batch047.root Batch047.certificate Batch047.checked p hL50 hi hr
                        · rcases CertificateBox.contains_lower_or_upper hU50 .k (15873 / 4096) with hL51 | hU51
                          · exact box_sound Batch048.root Batch048.certificate Batch048.checked p hL51 hi hr
                          · exact box_sound Batch049.root Batch049.certificate Batch049.checked p hU51 hi hr
                      · exact box_sound Batch050.root Batch050.certificate Batch050.checked p hU49 hi hr
                  · exact box_sound Batch051.root Batch051.certificate Batch051.checked p hU46 hi hr
      · rcases CertificateBox.contains_lower_or_upper hU15 .s (69 / 1280) with hL52 | hU52
        · exact box_sound Batch052.root Batch052.certificate Batch052.checked p hL52 hi hr
        · rcases CertificateBox.contains_lower_or_upper hU52 .k (1537 / 512) with hL53 | hU53
          · rcases CertificateBox.contains_lower_or_upper hL53 .chi (3 / 8) with hL54 | hU54
            · exact box_sound Batch053.root Batch053.certificate Batch053.checked p hL54 hi hr
            · exact box_sound Batch054.root Batch054.certificate Batch054.checked p hU54 hi hr
          · rcases CertificateBox.contains_lower_or_upper hU53 .chi (3 / 8) with hL55 | hU55
            · exact box_sound Batch055.root Batch055.certificate Batch055.checked p hL55 hi hr
            · exact box_sound Batch056.root Batch056.certificate Batch056.checked p hU55 hi hr
    · exact box_sound Batch057.root Batch057.certificate Batch057.checked p hU14 hi hr

end CourtadeKumar.LRDeterminantReducedCertificate

namespace CourtadeKumar.LRAnalyticDeterminant

/-- The entire compressed finite determinant input, with no free certificate. -/
theorem finite : LRDeterminantKLeFourFiniteCompressedCertificateTheorem := by
  intro p hi hr hregion hsk hk
  rcases hregion with ⟨hsLo, hsHi, hgate⟩
  by_cases hs : (1 / 128 : ℝ) ≤ p.s
  · have hp : LRDeterminantReducedCertificate.mainRoot.Contains p := by
      norm_num only [LRDeterminantReducedCertificate.mainRoot, CertificateBox.Contains,
        Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_one]
      exact ⟨hs, hsHi, hs.trans hsk.le, hk, hi.2.2.1.le, hi.2.2.2.le⟩
    exact Or.inr (LRDeterminantReducedCertificate.main p hp hi hr)
  · have hkOne : 1 ≤ p.k := hgate.resolve_left hs
    have hp : LRDeterminantReducedCertificate.tinyRoot.Contains p := by
      norm_num only [LRDeterminantReducedCertificate.tinyRoot, CertificateBox.Contains,
        Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_one]
      exact ⟨hsLo, (lt_of_not_ge hs).le, hkOne, hk, hi.2.2.1.le, hi.2.2.2.le⟩
    exact Or.inr (LRDeterminantReducedCertificate.tiny p hp hi hr)

end CourtadeKumar.LRAnalyticDeterminant
