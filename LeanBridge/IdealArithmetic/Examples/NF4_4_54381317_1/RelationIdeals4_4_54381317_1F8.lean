/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F8
import LeanBridge.IdealArithmetic.Examples.NF4_4_54381317_1.ClassGroupData4_4_54381317_1

set_option linter.all false

noncomputable section


noncomputable def E421RS1 : RelationCertificate Table 3 ![![421, 0, 0, 0], ![-210, 1, 0, 0]] 
  ![-76, -50, -6, 1] ![![3, 0, 0, 0], ![-1, 1, 0, 0]] where
    su := ![![1263, 0, 0, 0], ![-630, 3, 0, 0]]
    hsu := by decide  
    w := ![![-228, -150, -18, 3], ![459, 306, 36, -6]]
    hw := by decide  
    g := ![![![1042147, 10424345, -11467200, 282], ![3127400, 34400752, -842, 0]], ![![-517359, -5175038, 5692751, -140], ![-1552559, -17077832, 418, 0]]]
    h := ![![![-95206, 27015, -126, 0], ![-190865, 53250, 1, 0]], ![![192933, -52782, 456, -1], ![386784, -103974, 419, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R421N1 : Ideal.span {3} * I421N1 =  Ideal.span {B.equivFun.symm ![-76, -50, -6, 1]} * (J0 ^ 1*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E421RS1 


noncomputable def E421RS2 : RelationCertificate Table 3 ![![421, 0, 0, 0], ![-165, 1, 0, 0]] 
  ![-623, -285, -14, 4] ![![3, 0, 0, 0], ![1, 1, 0, 0]] where
    su := ![![1263, 0, 0, 0], ![-495, 3, 0, 0]]
    hsu := by decide  
    w := ![![-1869, -855, -42, 12], ![909, 420, 21, -6]]
    hw := by decide  
    g := ![![![549970, -5508528, -6058766, 215], ![-1652850, 18176808, -620, 0]], ![![-214658, 2150103, 2364870, -84], ![645149, -7094808, 242, 0]]]
    h := ![![![-51233, 6245153, -42796, 30], ![-130718, 15933812, -12626, 0]], ![![25368, -3037105, 20880, -15], ![64725, -7748828, 6313, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R421N2 : Ideal.span {3} * I421N2 =  Ideal.span {B.equivFun.symm ![-623, -285, -14, 4]} * (J0 ^ 0*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E421RS2 


noncomputable def E431RS1 : RelationCertificate Table 9 ![![431, 0, 0, 0], ![70, 1, 0, 0]] 
  ![637, 364, 29, -6] ![![9, 0, 0, 0], ![-128, -67, -4, 1]] where
    su := ![![3879, 0, 0, 0], ![630, 9, 0, 0]]
    hsu := by decide  
    w := ![![5733, 3276, 261, -54], ![1575, 774, 18, -9]]
    hw := by decide  
    g := ![![![-89103, -23840947, -6966971, 53455], ![181853810, 60778310, 0, 0]], ![![-14659, -3943779, -1152489, 8842], ![30082658, 10054080, 0, 0]]]
    h := ![![![22547, -1410530, -20714, -8], ![-138816, 8686823, 3442, 0]], ![![6125, -387794, -5751, -3], ![-37710, 2388243, 1292, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R431N1 : Ideal.span {9} * I431N1 =  Ideal.span {B.equivFun.symm ![637, 364, 29, -6]} * (J0 ^ 2*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E431RS1 


noncomputable def E431RS2 : RelationCertificate Table 9 ![![431, 0, 0, 0], ![-190, 1, 0, 0]] 
  ![-46, -19, -2, 0] ![![9, 0, 0, 0], ![-128, -67, -4, 1]] where
    su := ![![3879, 0, 0, 0], ![-1710, 9, 0, 0]]
    hsu := by decide  
    w := ![![-414, -171, -18, 0], ![909, 432, 9, -9]]
    hw := by decide  
    g := ![![![-182205, -48732186, -14240864, 109268], ![371718680, 124234013, 0, 0]], ![![80086, 21374336, 6246139, -47927], ![-163038162, -54489827, 0, 0]]]
    h := ![![![-171746, 7051423, -43188, 32], ![-389592, 15993546, -13792, 0]], ![![377491, -15470160, 94901, -71], ![856308, -35088330, 30600, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R431N2 : Ideal.span {9} * I431N2 =  Ideal.span {B.equivFun.symm ![-46, -19, -2, 0]} * (J0 ^ 2*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E431RS2 


noncomputable def E433RS1 : RelationCertificate Table 3 ![![433, 0, 0, 0], ![-185, 1, 0, 0]] 
  ![-22, -7, 1, 0] ![![3, 0, 0, 0], ![-131, -67, -4, 1]] where
    su := ![![1299, 0, 0, 0], ![-555, 3, 0, 0]]
    hsu := by decide  
    w := ![![-66, -21, 3, 0], ![-948, -546, -42, 9]]
    hw := by decide  
    g := ![![![-2079997, 4408845, 1333283, -65801], ![-9433613, -3210304, 0, 0]], ![![888689, -1883313, -569553, 28108], ![4029897, 1371392, 0, 0]]]
    h := ![![![-12874, -300, -659893, 3567], ![-30132, -865, -1544511, 0]], ![![-189492, -10400, -14015722, 75761], ![-443512, -26738, -32804510, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R433N1 : Ideal.span {3} * I433N1 =  Ideal.span {B.equivFun.symm ![-22, -7, 1, 0]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E433RS1 


noncomputable def E433RS2 : RelationCertificate Table 3 ![![433, 0, 0, 0], ![-73, 1, 0, 0]] 
  ![-165, -76, -4, 1] ![![3, 0, 0, 0], ![-131, -67, -4, 1]] where
    su := ![![1299, 0, 0, 0], ![-219, 3, 0, 0]]
    hsu := by decide  
    w := ![![-495, -228, -12, 3], ![933, 402, 15, -6]]
    hw := by decide  
    g := ![![![2855283, -6051764, -1830071, 90323], ![12948188, 4406376, 0, 0]], ![![-474601, 1005960, 304203, -15014], ![-2152307, -732448, 0, 0]]]
    h := ![![![-68733, 5370030, -75520, 27], ![-407688, 31846786, -11690, 0]], ![![129907, -10123472, 142522, -53], ![770540, -60036890, 22947, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R433N2 : Ideal.span {3} * I433N2 =  Ideal.span {B.equivFun.symm ![-165, -76, -4, 1]} * (J0 ^ 1*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E433RS2 


noncomputable def E439RS1 : RelationCertificate Table 9 ![![439, 0, 0, 0], ![31, 1, 0, 0]] 
  ![-122, -72, -5, 1] ![![9, 0, 0, 0], ![279, 94, 0, -1]] where
    su := ![![3951, 0, 0, 0], ![279, 9, 0, 0]]
    hsu := by decide  
    w := ![![-1098, -648, -45, 9], ![432, -144, -18, 9]]
    hw := by decide  
    g := ![![![-953923593590, 2784965137931, 571955130526, -93505401198], ![-473828241864, -367590636894, 9979384, 0]], ![![-67975553519, 198453573523, 40756897833, -6663092749], ![-33764482927, -26194107252, 711120, 0]]]
    h := ![![![-1500, 61830, 1996, 0], ![21238, -876280, 1, 0]], ![![549, -24625, -826, -1], ![-7773, 348972, 440, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R439N1 : Ideal.span {9} * I439N1 =  Ideal.span {B.equivFun.symm ![-122, -72, -5, 1]} * (J0 ^ 1*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E439RS1 


noncomputable def E439RS2 : RelationCertificate Table 9 ![![439, 0, 0, 0], ![50, 1, 0, 0]] 
  ![-94, -53, -3, 1] ![![9, 0, 0, 0], ![-427, -210, -11, 3]] where
    su := ![![3951, 0, 0, 0], ![450, 9, 0, 0]]
    hsu := by decide  
    w := ![![-846, -477, -27, 9], ![-3141, -1656, -90, 27]]
    hw := by decide  
    g := ![![![-7419191805, 21685351519, 2398314845, 521556490], ![-156749499222, -58194308850, 836, 0]], ![![-860839114, 2516123879, 278273427, 60515534], ![-18187444945, -6752211611, 97, 0]]]
    h := ![![![-71496, 14910226, 302033, 76], ![627733, -130924340, -33363, 0]], ![![-265341, 55363011, 1121516, 283], ![2329687, -486133834, -124234, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R439N2 : Ideal.span {9} * I439N2 =  Ideal.span {B.equivFun.symm ![-94, -53, -3, 1]} * (J0 ^ 2*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E439RS2 


noncomputable def E449RS1 : RelationCertificate Table 9 ![![449, 0, 0, 0], ![82, 1, 0, 0]] 
  ![179, 84, 2, -1] ![![9, 0, 0, 0], ![279, 94, 0, -1]] where
    su := ![![4041, 0, 0, 0], ![738, 9, 0, 0]]
    hsu := by decide  
    w := ![![1611, 756, 18, -9], ![12024, 7011, 585, -117]]
    hw := by decide  
    g := ![![![11957906439352900770801, -34910780539634349569212, -7169366658590662817593, 1172224792072713820381], ![5941144562417526863766, 4608878566236738357882, -12243220, 0]], ![![2202149106682717583962, -6429114040058709386937, -1320299206451280164596, 215875060721243917835], ![1094111770915364406149, 848763775575801543384, -2254692, 0]]]
    h := ![![![6819, -431498, -5509, -3], ![-37336, 2363171, 1346, 0]], ![![52140, -3216757, -40546, -16], ![-285482, 17617197, 7171, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R449N1 : Ideal.span {9} * I449N1 =  Ideal.span {B.equivFun.symm ![179, 84, 2, -1]} * (J0 ^ 1*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E449RS1 


noncomputable def E449RS2 : RelationCertificate Table 9 ![![449, 0, 0, 0], ![-105, 1, 0, 0]] 
  ![-368, -151, -6, 2] ![![9, 0, 0, 0], ![-427, -210, -11, 3]] where
    su := ![![4041, 0, 0, 0], ![-945, 9, 0, 0]]
    hsu := by decide  
    w := ![![-3312, -1359, -54, 18], ![18873, 8883, 450, -126]]
    hw := by decide  
    g := ![![![2766068095483, -8084863616216, -894154494142, -194449856898], ![58440292519687, 21696353602940, -1068, 0]], ![![-639718404685, 1869815160175, 206794289668, 44971109905], ![-13515694276638, -5017792854418, 247, 0]]]
    h := ![![![-735802, 41538440, -416012, 195], ![-3146426, 177596317, -87553, 0]], ![![4193298, -236570091, 2369845, -1116], ![17931321, -1011448005, 501070, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R449N2 : Ideal.span {9} * I449N2 =  Ideal.span {B.equivFun.symm ![-368, -151, -6, 2]} * (J0 ^ 2*J1^ 1) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E449RS2 


noncomputable def E457RS1 : RelationCertificate Table 9 ![![457, 0, 0, 0], ![-116, 1, 0, 0]] 
  ![590, 331, 21, -5] ![![9, 0, 0, 0], ![-4, 1, 0, 0]] where
    su := ![![4113, 0, 0, 0], ![-1044, 9, 0, 0]]
    hsu := by decide  
    w := ![![5310, 2979, 189, -45], ![-4275, -2394, -153, 36]]
    hw := by decide  
    g := ![![![-8551047314018925443, -207362897364958939130, 52375164798444656200, -19684649], ![-19239856456542581927, -471376483185293258417, 177161845, 0]], ![![2179862205548977168, 52861658484562695507, -13351656009007557257, 5018078], ![4904689962485198546, 120164904080887364500, -45162703, 0]]]
    h := ![![![677190, 19425, 48850397, -421126], ![2667890, 99524, 192454577, 0]], ![![-544983, -15489, -39265129, 338494], ![-2147041, -79528, -154691754, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R457N1 : Ideal.span {9} * I457N1 =  Ideal.span {B.equivFun.symm ![590, 331, 21, -5]} * (J0 ^ 2*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E457RS1 


noncomputable def E457RS2 : RelationCertificate Table 9 ![![457, 0, 0, 0], ![-93, 1, 0, 0]] 
  ![-274, -138, -7, 2] ![![9, 0, 0, 0], ![-2, 1, 0, 0]] where
    su := ![![4113, 0, 0, 0], ![-837, 9, 0, 0]]
    hsu := by decide  
    w := ![![-2466, -1242, -63, 18], ![1314, 666, 36, -9]]
    hw := by decide  
    g := ![![![1765396, 75046653, -37965452, 284], ![7946208, 341683927, -2532, 0]], ![![-354190, -15056758, 7617084, -57], ![-1594257, -68552724, 508, 0]]]
    h := ![![![-11800, -953, -2536842, 27278], ![-57982, -5305, -12466044, 0]], ![![6422, 564, 1356398, -14585], ![31556, 3110, 6665344, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R457N2 : Ideal.span {9} * I457N2 =  Ideal.span {B.equivFun.symm ![-274, -138, -7, 2]} * (J0 ^ 0*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E457RS2 


noncomputable def E463RS0 : RelationCertificate Table 9 ![![463, 0, 0, 0], ![59, 1, 0, 0]] 
  ![-13, -4, 1, 0] ![![9, 0, 0, 0], ![-128, -67, -4, 1]] where
    su := ![![4167, 0, 0, 0], ![531, 9, 0, 0]]
    hsu := by decide  
    w := ![![-117, -36, 9, 0], ![-1017, -558, -36, 9]]
    hw := by decide  
    g := ![![![120, 128, 42, 1], ![-1455, -463, 0, 0]], ![![30, 25, 6, 0], ![-187, -60, 0, 0]]]
    h := ![![![-5420, 498, -2398340, -40650], ![42533, -4629, 18820950, 0]], ![![-100058, 21110990, 363506, 96], ![785199, -165680909, -44447, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R463N0 : Ideal.span {9} * I463N0 =  Ideal.span {B.equivFun.symm ![-13, -4, 1, 0]} * (J0 ^ 2*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E463RS0 


noncomputable def E463RS1 : RelationCertificate Table 9 ![![463, 0, 0, 0], ![125, 1, 0, 0]] 
  ![-292, -147, -7, 2] ![![9, 0, 0, 0], ![-2, 1, 0, 0]] where
    su := ![![4167, 0, 0, 0], ![1125, 9, 0, 0]]
    hsu := by decide  
    w := ![![-2628, -1323, -63, 18], ![1350, 666, 27, -9]]
    hw := by decide  
    g := ![![![388512, 16535632, -8366305, 536], ![1750960, 75287048, -4790, 0]], ![![105122, 4473944, -2263619, 145], ![473752, 20369948, -1296, 0]]]
    h := ![![![-451884, 116346954, 993929, 505], ![1673776, -430962509, -233813, 0]], ![![232050, -59768428, -510662, -260], ![-859512, 221389134, 120379, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R463N1 : Ideal.span {9} * I463N1 =  Ideal.span {B.equivFun.symm ![-292, -147, -7, 2]} * (J0 ^ 0*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E463RS1 


noncomputable def E463RS2 : RelationCertificate Table 9 ![![463, 0, 0, 0], ![127, 1, 0, 0]] 
  ![-162, -76, -4, 1] ![![9, 0, 0, 0], ![-128, -67, -4, 1]] where
    su := ![![4167, 0, 0, 0], ![1143, 9, 0, 0]]
    hsu := by decide  
    w := ![![-1458, -684, -36, 9], ![54, -27, -9, 0]]
    hw := by decide  
    g := ![![![186635, 49883606, 14577320, -111849], ![-380501153, -127169282, 0, 0]], ![![51633, 13769172, 4023705, -30874], ![-105027736, -35101872, 0, 0]]]
    h := ![![![-13560, 1360988, 11352, 5], ![49434, -4962102, -2314, 0]], ![![474, -50796, -527, -1], ![-1728, 185199, 463, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R463N2 : Ideal.span {9} * I463N2 =  Ideal.span {B.equivFun.symm ![-162, -76, -4, 1]} * (J0 ^ 2*J1^ 2) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E463RS2 


noncomputable def E463RS3 : RelationCertificate Table 9 ![![463, 0, 0, 0], ![151, 1, 0, 0]] 
  ![-571, -281, -15, 4] ![![9, 0, 0, 0], ![-4, 1, 0, 0]] where
    su := ![![4167, 0, 0, 0], ![1359, 9, 0, 0]]
    hsu := by decide  
    w := ![![-5139, -2529, -135, 36], ![3816, 1881, 99, -27]]
    hw := by decide  
    g := ![![![84305978734, 2044419986460, -516374123689, 847], ![189688452401, 4647367082728, -7620, 0]], ![![27570927241, 668594986230, -168871930623, 277], ![62034586373, 1519847365641, -2492, 0]]]
    h := ![![![-16803, 391935, 2746, 1], ![51518, -1202104, -459, 0]], ![![11760, -291201, -2230, -2], ![-36056, 893128, 923, 0]]]
    hle1 := by decide  
    hle2 := by decide  

lemma R463N3 : Ideal.span {9} * I463N3 =  Ideal.span {B.equivFun.symm ![-571, -281, -15, 4]} * (J0 ^ 2*J1^ 0) := by 
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E463RS3 
