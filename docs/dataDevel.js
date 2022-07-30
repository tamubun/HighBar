'use strict';

var params = {
  fps: 240, // シミュレーション精度(単位 1/秒)

  /* 全体重。各パーツの重さの違いが大きいと、なぜか手とバーとの接合部が
     引っ張られすぎてしまうので、実際の体重比
     (http://www.tukasa55.com/staff-blog/?p=5666等)からずらさないといかん */
  total_weight: 68.0,

  /* 最初に選手モデルをtamubunの体格に合わせて作ったため、本来のバーの高さ 2.8m
     ではバーが低く見えてしまう。選手モデルを作り直すのではなく、
     バーの大きさを scale倍することにする。 */
  scale: 3.2 / 2.8,
  bar: {size: [0.024, 2.4, 2.8], mass: 10, color: 0xffffff},
  pole: {size: 0.04, color: 0x5080e0}, // 太さ適当。色も。
  /* ワイヤーの位置 FIG Apparatus Norms p46 参照。
     https://www.gymnastics.sport/publicdir/rules/files/en_Apparatus Norms.pdf
   */
  wire: {dist_x: 1.55, dist_z: 2.0, middle_y_from_top: 0.35 /* これは規則なし */,
         color: 0x555555},
  floor: {size: [1.5, 0.09, 6.0], color: 0xccdea0},
  landing: {air_max: 200}, // 空気抵抗の最大値(N)。体重は約666N

  // 骨盤
  pelvis: {size: [0.16, 0.10, 0.10], ratio: 0.14, color: 0x0000ff},

  // 脊椎
  spine: {size: [0.14, 0.10, 0.09], ratio: 0.13, color: 0xffffff},

  // 胸
  chest: {size: [0.1505, 0.10, 0.105], ratio: 0.17, color: 0xffffff},

  // 頭
  head: {size: [0.09, 0.14, 0.11], ratio: 0.08, color: 0x888800},

  // 上肢
  upper_leg: {size: [0.08, 0.50], ratio: 0.07, color: 0x888800, x: 0.08},

  // 下肢
  lower_leg: {size: [0.05, 0.60], ratio: 0.07, color: 0x888800, x: 0.065},

  // 上腕
  upper_arm: {size: [0.045, 0.30], ratio: 0.05, color: 0x888800},

  // 下腕
  lower_arm: {size: [0.03, 0.40], ratio: 0.05, color: 0x888800},

  // 手(物理的な実態無し)
  hand: {size: 0.05, color: 0xcc7700},

  // 初期状態(後振り下しなど)に持っていく時の力
  helper_impulse: 200,

  // 調整可能なパラメーター。gui_paramsのデフォルト、最小値、最大値、刻み幅。
  adjustable: {
    '首の力': [0.7, [0.3, 1.2, 0.02]],
    '肩の力': [0.8, [0.3, 1.2, 0.02]],
    '胸の力': [1.1, [0.7, 1.5, 0.02]],
    '腹の力': [1.1, [0.7, 1.5, 0.02]],
    '肘の力': [0.7, [0.3, 1.2, 0.02]],
    '膝の力': [1.3, [0.9, 1.7, 0.02]],
    '屈身にする時間': [0.08, [0.01, 1.5]],
    '腰の力の最大値': [80, [60, 160]],
    '手首の力の最大値': [8, [6, 10]],
    '時間の流れ': [1.0, [0.1, 1.2, 0.02]],
    'キャッチ時間': [5, [0.1, 5]], // バーキャッチ動作の許容時間(秒)
    'キャッチ幅': [30, [2, 80]], // バーキャッチ出来る範囲(cm)
    '着地空気抵抗': [60.0, [0, 100, 0.1]], // 空気抵抗
    '着地補助範囲': [20.0, [5, 40, 0.1]],
    'バー弾性': [4.5, [1, 8, 0.05]],
    'バー減衰': [5, [2, 8, 0.05]],
    'マット摩擦': [7, [0, 40, 0.1]]
  },

  // 力の最大値 (6DofConstraintは max impulse でなく、max force)
  max_force: {
    hip: [80, 10],        // 尻(懸垂で脚前挙で維持出来るより少し強め)
    hip_init: [200, 200], // 尻(初期状態に持っていく時だけ力持ちにする)
    hip_landing_min: 110, // 着地の時だけは最低限これだけの力を付ける。
    grip: [8.0, 1.0] },   // 手首。grip[0]はGUIで上書きする。

  // 柔軟性
  flexibility: {
    knee: [-4, 170],      // 膝
//  shoulder: [-20, 290], // 肩の柔軟性は当面無視する。無限アドラー可能
    shoulder: {           // 肩
      shift_min: [0, 0, 0],
      shift_max: [0, 0, 0],
      angle_min: [+10, 0, 0],   // 無限アドラー可能。y, z軸周りの自由度は当面無し。
      angle_max: [-10, 0, 0] },
    hip: {                // 尻
      shift_min: [0, 0, 0],          // 最小ズレ
      shift_max: [0, 0, 0],          // 最大ズレ
      angle_min: [-160, -85, -10],   // 最小角度
      angle_max: [  90,  10,   2] }, // 最大角度
    elbow: [-2, 150],     // 肘
    neck: [90, 60, 60],   // 首
    breast: [45, 45, 45], // 胸、脊椎の間
    belly: [45, 45, 45],  // 脊椎、骨盤の間
    hip: {                // 尻
      shift_min: [0, 0, 0],          // 最小ズレ
      shift_max: [0, 0, 0],          // 最大ズレ
      angle_min: [-160, -85, -10],   // 最小角度
      angle_max: [  90,  10,   2] }, // 最大角度
    grip: {
      shift_min: [0, 0, 0],          // 最小ズレ
      shift_max: [0, 0, 0],          // 最大ズレ
      angle_min: [ 0, -30, -170],     // 最小角度
      angle_max: [-1,  30, 170] },    // 最大角度
  }
};

var dousa_dict = {
  "直線": {
    "shoulder": [[0, 0.1], [0, 0.1]],
    "hip": [[0, 0, 0.2, 0.2], [0, 0, 0.2, 0.2]],
    "neck": [0, 0, 0],
    "breast": [0, 0, 0],
    "belly": [0, 0, 0],
    "knee": [[0, 0.1], [0, 0.1]],
    "elbow": [[0, 0.1], [0, 0.1]],
    "grip": [[0, 0, 0.2, 0.2], [0, 0, 0.2, 0.2]] },
  "押し": {
    "shoulder": [[5, 0.3], [5, 0.3]],
    "hip": [[4, 0, 0.3, 0.2], [4, 0, 0.3, 0.2]],
    "neck": [0, 0, 3],
    "breast": [0, 0, 2],
    "belly": [0, 0, 2],
    "knee": [[0, 0.1], [0, 0.1]],
    "elbow": [[0, 0.1], [0, 0.1]],
    "grip": [[0, 0, 0.2, 0.2], [0, 0, 0.2, 0.2]] },
  "押し(肩角度有り)": {
    "shoulder": [[85, 0.4], [85, 0.4]],
    "hip": [[-10, 0, 0.6, 0.2], [-10, 0, 0.6, 0.2]],
    "neck": [0, 0, 0],
    "breast": [0, 0, 15],
    "belly": [0, 0, -15],
    "knee": [[0, 0.1], [0, 0.1]],
    "elbow": [[0, 0.1], [0, 0.1]],
    "grip": [[0, 0, 0.2, 0.2], [0, 0, 0.2, 0.2]] },
  "抜き": {
    "shoulder": [[-10, 0.3], [-10, 0.3]],
    "hip": [[-15, 0, 0.3, 0.2], [-15, 0, 0.3, 0.2]],
    "neck": [0, 0, 3],
    "breast": [0, 0, -10],
    "belly": [0, 0, -10],
    "knee": [[0, 0.1], [0, 0.1]],
    "elbow": [[0, 0.1], [0, 0.1]],
    "grip": [[0, 0, 0.2, 0.2], [0, 0, 0.2, 0.2]] },
  "あふり": {
    "shoulder": [[20, 0.35], [20, 0.35]],
    "hip": [[20, 0, 0.1, 0.2], [20, 0, 0.1, 0.2]],
    "neck": [0, 0, 5],
    "breast": [0, 0, 15],
    "belly": [0, 0, 15],
    "knee": [[0, 0.1], [0, 0.1]],
    "elbow": [[0, 0.1], [0, 0.1]],
    "grip": [[0, 0, 0.2, 0.2], [0, 0, 0.2, 0.2]] },
  "あふり終り": {
    "shoulder": [[10, 0.8], [10, 0.8]],
    "hip": [[10, 0, 0.2, 0.2], [10, 0, 0.2, 0.2]],
    "neck": [0, 0, 3],
    "breast": [0, 0, 7],
    "belly": [0, 0, 7],
    "knee": [[0, 0.1], [0, 0.1]],
    "elbow": [[0, 0.1], [0, 0.1]],
    "grip": [[0, 0, 0.2, 0.2], [0, 0, 0.2, 0.2]] },
  "脚引き寄せ": {
    "shoulder": [[40, 0.17], [40, 0.17]],
    "hip": [[120, 0, 0.15, 0.2], [120, 0, 0.15, 0.2]],
    "neck": [0, 0, 10],
    "breast": [0, 0, 35],
    "belly": [0, 0, 45],
    "knee": [[0, 0.1], [0, 0.1]],
    "elbow": [[0, 0.1], [0, 0.1]],
    "grip": [[0, 0, 0.2, 0.2], [0, 0, 0.2, 0.2]] },
  "蹴り": {
    "shoulder": [[170, 0.15], [170, 0.15]],
    "hip": [[60, 0, 0.07, 0.2], [60, 0, 0.07, 0.2]],
    "neck": [0, 0, 10],
    "breast": [0, 0, 15],
    "belly": [0, 0, 15],
    "knee": [[0, 0.1], [0, 0.1]],
    "elbow": [[0, 0.1], [0, 0.1]],
    "grip": [[0, 0, 0.2, 0.2], [0, 0, 0.2, 0.2]] },
  "支持振り出し": {
    "shoulder": [[20, 0.25], [20, 0.25]],
    "hip": [[20, 0, 0.3, 0.2], [20, 0, 0.3, 0.2]],
    "neck": [0, 0, 10],
    "breast": [0, 0, 15],
    "belly": [0, 0, 15],
    "knee": [[0, 0.1], [0, 0.1]],
    "elbow": [[0, 0.1], [0, 0.1]],
    "grip": [[0, 0, 0.2, 0.2], [0, 0, 0.2, 0.2]] },
  "伸身": {
    "hip": [[-5, 0, 0.1, 0.1], [-5, 0, 0.1, 0.1]],
    "breast": [0, 0, 7],
    "belly": [0, 0, -2],
    "knee": [[0, 0.1], [0, 0.1]],
    "elbow": [[0, 0.1], [0, 0.1]] },
  "閉脚浮腰": {
    "shoulder": [[130, 0.05], [130, 0.05]],
    "hip": [[20, 0, 0.22, 0.2], [20, 0, 0.22, 0.2]],
    "neck": [0, 0, 0],
    "breast": [0, 0, 25],
    "belly": [0, 0, 25],
    "knee": [[0, 0.1], [0, 0.1]],
    "elbow": [[0, 0.1], [0, 0.1]],
    "grip": [[0, 0, 0.2, 0.2], [0, 0, 0.2, 0.2]] },
  "開脚": {
    "shoulder": [[40, 0.15], [40, 0.15]],
    "hip": [[160, 35, 0.1, 0.1], [160, 35, 0.1, 0.1]],
    "neck": [0, 0, 5],
    "breast": [0, 0, 25],
    "belly": [0, 0, 30],
    "knee": [[0, 0.1], [0, 0.1]],
    "elbow": [[0, 0.1], [0, 0.1]],
    "grip": [[0, 0, 0.2, 0.2], [0, 0, 0.2, 0.2]] },
  "背倒立": {
    "shoulder": [[35, 0.15], [35, 0.15]],
    "hip": [[0, 0, 0.3, 0.3], [0, 0, 0.3, 0.3]],
    "neck": [0, 0, 10],
    "breast": [0, 0, 5],
    "belly": [0, 0, 5],
    "knee": [[0, 0.1], [0, 0.1]],
    "elbow": [[0, 0.1], [0, 0.1]],
    "grip": [[0, 0, 0.2, 0.2], [0, 0, 0.2, 0.2]] },
  "抱え込み(弱)": {
    "shoulder": [[130, 0.35], [130, 0.35]],
    "hip": [[60, 0, 0.15, 0.2], [60, 0, 0.15, 0.2]],
    "neck": [0, 0, -45],
    "breast": [0, 0, 15],
    "belly": [0, 0, 15],
    "knee": [[120, 0.1], [120, 0.1]],
    "elbow": [[0, 0.1], [0, 0.1]] },
  "抱え込み(強)": {
    "shoulder": [[140, 0.3], [140, 0.3]],
    "hip": [[100, 0, 0.15, 0.2], [100, 0, 0.15, 0.2]],
    "neck": [0, 0, -45],
    "breast": [0, 0, 35],
    "belly": [0, 0, 35],
    "knee": [[130, 0.1], [130, 0.1]],
    "elbow": [[0, 0.1], [0, 0.1]] },
  "屈身(弱)": {
    "shoulder": [[130, 0.35], [130, 0.35]],
    "hip": [[105, 0, 0.08, 0.2], [105, 0, 0.08, 0.2]],
    "neck": [0, 0, -25],
    "breast": [0, 0, 15],
    "belly": [0, 0, 15],
    "knee": [[0, 0.1], [0, 0.1]],
    "elbow": [[0, 0.1], [0, 0.1]] },
  "屈身(強)": {
    "shoulder": [[130, 0.35], [130, 0.35]],
    "hip": [[150, 0, 0.08, 0.2], [150, 0, 0.08, 0.2]],
    "neck": [0, 0, -25],
    "breast": [0, 0, 15],
    "belly": [0, 0, 15],
    "knee": [[0, 0.1], [0, 0.1]],
    "elbow": [[0, 0.1], [0, 0.1]] },
  "離手": {
    "grip": ["release", "release"] },
  "片手離手": {
    "grip": ["release", [0, 0, 0.2, 0.2]] },
  "バーキャッチ": {
    "grip": ["catch", "catch"] },
  "捻り": {
    "shoulder": [[160, 0.6], [160, 0.05]] },
  "着地": {
    "shoulder": [[35, 0.1], [35, 0.1]],
    "hip": [[55, 0, 0.2, 0.2], [55, 0, 0.2, 0.2]],
    "neck": [0, 0, -25],
    "breast": [0, 0, 30],
    "belly": [0, 0, 20],
    "knee": [[50, 0.1], [50, 0.1]],
    "elbow": [[0, 0.1], [0, 0.1]],
    "landing": true }
};

var start_list = [
  '後振り下し', '前振り下し', '小スイング', '静止'
];

var waza_list = [
  '車輪', '加速車輪', '真っ直ぐ', 'ツイスト',
  '蹴上り', '翻転', '翻転(改)', 'シュタルダー', '閉脚シュタルダー', 'エンドー',
  '離手', '片手離手',
  'バーキャッチ', 'バーキャッチ(左のみ)', 'バーキャッチ(右のみ)',
  '着地',
  '抱え込み(弱)', '抱え込み(強)', '屈身(弱)','屈身(強)',
  'アドラー', 'アドラー(改)',
  'トカチェフ',
  '抱え込み宙返り降り', '伸身宙返り半捻り降り', '伸身ムーンサルト', '行進',
  '捻り1', '捻り2', '捻り3', '捻り4', '捻り5', '捻り6'];

var waza_dict = {
  '後振り下し': [['直線', {angle: -160}]],
  '前振り下し': [['直線', {angle: 160}]],
  '小スイング': [['直線', {angle: -45}]],
  '静止': [['直線', {angle: 0}]],
  '車輪' : [['押し', {}], ['抜き', {}], ['あふり', {}], ['あふり終り', {}]],
  '真っ直ぐ': [['押し', {}], ['直線', {}]],
  'ツイスト': [
    ["押し", {}],
    ["抜き",
     { "shoulder": [[-30, 0.1], [30, 0.2]],
       "hip": [[-5, 0, 0.15, 0.3], [-5, 0, 0.15, 0.3]] }],
    ["あふり",
     { "shoulder": [[150, 0.01], [50, 0.2]],
       "hip": [[120, 0, 0.05, 0.1], [120, 0, 0.05, 0.1]],
       "neck": [0, 0, -20],
       "breast": [0, 0, 40],
       "belly": [0, 0, 40] }],
    ["あふり",
     { "shoulder": [[150, 0.01], [10, 0.1]],
       "hip": [[120, 0, 0.01, 0.1], [120, 0, 0.01, 0.1]],
       "neck": [0, 0, -20],
       "breast": [0, 0, 40],
       "belly": [0, 0, 40] }],
    ["押し",
     { "shoulder": [[-10, 0.01], [10, 0.01]],
       "hip": [[5, 0, 0.1, 0.2], [5, 0, 0.1, 0.2]] }],
    ["片手離手",
     { "neck": [5, 45, 0] }],
    ["直線", {}],
    ["バーキャッチ", {}] ],
  '蹴上り': [
    ['押し', {}],
    ['抜き', {}],
    ['脚引き寄せ', {}],
    ['蹴り', {}],
    ['支持振り出し', {}]],
  '翻転': [
    ['押し(肩角度有り)',
     { shoulder: [[140, 0.55], [140, 0.55]],
       hip: [[-15, 0, 0.6, 0.2], [-15, 0, 0.6, 0.2]],
       breast: [0, 0, 10] }],
    ['閉脚浮腰', {}],
    ['背倒立',
     { shoulder: [[60, 0.2], [60, 0.2]],
       hip: [[0, 0, 0.2, 0.2], [0, 0, 0.2, 0.2]] }],
    ['押し', { shoulder: [[5, 0.2], [5, 0.2]] }] ],
  '翻転(改)': [
    ['押し(肩角度有り)',
     { shoulder: [[150,0.5], [150,0.5]],
       hip: [[-15,0,0.6,0.2], [-15,0,0.6,0.2]],
       breast: [0,0,10] }],
    ['閉脚浮腰',
      { shoulder: [[140,0.1], [140,0.1],6],
        hip: [[1,0,0.1,0.2], [1,0,0.1,0.2]],
        belly: [0,0,10] }],
    ['背倒立',
     { shoulder: [[60,0.3], [60,0.3]],
       hip: [[-20,0,0.05,0.2], [-20,0,0.05,0.2]] }],
    ['押し', {shoulder:[[5,0.2],[5,0.2]] }] ],
  'シュタルダー': [
    ['押し(肩角度有り)', {}],
    ['開脚', {}],
    ['背倒立', {}],
    ['押し',
     { shoulder: [[5, 0.25], [5, 0.25]],
       hip: [[4, 0, 0.35, 0.35], [4, 0, 0.35, 0.35]] }] ],
  '閉脚シュタルダー': [
    ['押し(肩角度有り)', {shoulder: [[120,0.3], [120,0.3]] }],
    ['開脚',
     { shoulder: [[10,0.1], [10,0.11]],
       hip: [[150,0,0.1,0.1], [150,0,0.1,0.1]] }],
    ['開脚',
     { shoulder: [[80,0.1], [80,0.1]],
       hip: [[150,0,0.5,0.1], [148,0,0.5,0.1]] }],
    ['押し',
     { shoulder: [[5,0.25], [5,0.25]],
       hip: [[4,0,0.35,0.35], [4,0,0.35,0.35]] }] ],
  'エンドー': [
    ['押し',
     { 'shoulder': [[30, 0.2], [30, 0.2]],
       'hip': [[160, 30, 0.15, 0.35], [160, 30, 0.15, 0.35]] }],
    ['開脚',
     { 'shoulder': [[100, 0.1], [100, 0.1]],
       'hip': [[130, 30, 0.1, 0.35], [130, 30, 0.1, 0.35]] }],
    ['背倒立',
     { 'shoulder': [[30, 0.2], [30, 0.2]],
       'hip': [[160, 30, 0.2, 0.35], [160, 30, 0.2, 0.35]] }],
    ['押し',
     { 'shoulder': [[5, 0.3], [5, 0.3]],
       'hip': [[4, 0, 0.3, 0.35], [4, 0, 0.3, 0.35]] }] ],
  '離手': [['離手', {}]], // もし、両手とも握ってたら、むしろ左手離手の動きになる
  '片手離手': [['片手離手', {}]],
  'バーキャッチ': [['バーキャッチ', {}]],
  'バーキャッチ(左のみ)': [ // もし、両手とも握ってたら、むしろ右手離手の動きになる
    ['バーキャッチ', { grip: ['catch', 'release']}]],
  'バーキャッチ(右のみ)': [ // もし、両手とも握ってたら、むしろ左手離手の動きになる
    ['バーキャッチ', { grip: ['release', 'catch']}]],
  '着地': [['着地', {}]],
  '抱え込み(弱)': [['抱え込み(弱)', {}]],
  '抱え込み(強)': [['抱え込み(強)', {}]],
  '屈身(弱)': [['屈身(弱)', {}]],
  '屈身(強)': [['屈身(強)', {}]],
  'アドラー': [
    ['押し', // アドラーは、部品名全部「押し」でバリエーションで全指定している。
     { shoulder: [[30, 0.1], [30, 0.1]],
       hip: [[120, 0, 0.1, 0.1], [120, 0, 0.1, 0.1]],
       neck: [0, 0, -20],
       breast: [0, 0, 20],
       belly: [0, 0, -10] }],
    ['押し',
     { shoulder: [[85, 0.07], [85, 0.07]],
       hip: [[160, 0, 0.1, 0.1], [160, 0, 0.1, 0.1]],
       neck: [0, 0, -20],
       breast: [0, 0, 40],
       belly: [0, 0, 40] }],
    ['押し',
     { shoulder: [[200, 0.1], [200, 0.1]],
       hip: [[120, 0, 0.07, 0.1], [120, 0, 0.07, 0.1]],
       neck: [0, 0, 20],
       breast: [0, 0, 40],
       knee: [[0, 0.1], [0, 0.1]],
       belly: [0, 0, 40] }],
    ['押し',
     { shoulder: [[370, 0.05], [370, 0.05]],
       hip: [[10, 0, 0.4, 0.1], [10, 0, 0.4, 0.1]],
       neck: [0, 0, 20],
       breast: [0, 0, -10],
       knee: [[0, 0.1], [0, 0.1]],
       belly: [0, 0, 10] }] ],
  'アドラー(改)': [
    ['押し', {}],
    ['押し', {
      'hip': [[30, 0, 0.1, 0.1], [30, 0, 0.1, 0.1]],
      'shoulder': [[10, 0.05], [10, 0.05]]}],
    ['押し', {}],
    ['抜き', {}],
    ['押し', {
      'shoulder': [[30, 0.1], [30, 0.1]],
      'hip': [[120, 0, 0.1, 0.1], [120, 0, 0.1, 0.1]],
      'neck': [0, 0, -20],
      'breast': [0, 0, 20],
      'belly': [0, 0, -10] }],
    ['押し', {
      'shoulder': [[85, 0.07], [85, 0.07]],
      'hip': [[160, 0, 0.1, 0.1], [160, 0, 0.1, 0.1]],
      'breast': [0, 0, 40],
      'belly': [0, 0, 40] }],
    ['押し', {
      'shoulder': [[200, 0.1], [200, 0.1]],
      'hip': [[120, 0, 0.07, 0.1], [120, 0, 0.07, 0.1]],
      'neck': [0, 0, 20],
      'knee': [[0, 0.1], [0, 0.1]] }],
    ['押し', {
      'shoulder': [[370, 0.2], [370, 0.2]],
      'hip': [[10, 0, 0.4, 0.1], [10, 0, 0.4, 0.1]],
      'breast': [0, 0, -10],
      'belly': [0, 0, 10] }],
    ['押し', {
      'shoulder': [[420, 0.001], [420, 0.001]],
      'hip': [[60, 0, 0.1, 0.1], [60, 0, 0.1, 0.1]] }],
    ['離手', {}],
    ['直線', {}],
    ['バーキャッチ', {}] ],
  '加速車輪': [
    ['押し', {}],
    ['抜き', {}],
    ['閉脚浮腰', {}],
    ['閉脚浮腰', {}],
    ['押し', {'shoulder': [[5,0.2], [5,0.2]] }] ],
  'トカチェフ': [
    ['押し', {}],
    ['抜き', {}],
    ['押し', {
      'shoulder': [[50,0.1], [50,0.1]],
      'hip': [[100,0,0.05,0.1], [100,0,0.05,0.1]],
      'neck': [0,0,-20],
      'breast': [0,0,20],
      'belly': [0,0,-10] }],
    ['押し', {
      'shoulder': [[50,0.2], [50,0.2]],
      'hip': [[95,0,0.1,0.1], [95,0,0.1,0.1]],
      'neck': [0,0,-20],
      'breast': [0,0,20],
      'belly': [0,0,-10] }],
    ['押し', {'shoulder': [[90,0.2], [90,0.2]]}],
    ['押し',{
      'neck': [0,0,-20],
      'shoulder': [[-30,0.15], [-30,0.15]],
      'hip': [[-15,0,0.1,0.2], [-15,0,0.1,0.2]] }],
    ['押し', {
      'shoulder': [[90,0.1], [90,0.1]],
      'hip': [[70,0,0.1,0.01], [70,0,0.1,0.01]],
      'neck': [0,0,1],
      'breast': [0,0,20],
      'belly': [0,0,-10] }],
    ['押し', {
      'shoulder': [[90,0.2], [90,0.2]],
      'hip': [[70,0,0.1,0.01], [70,0,0.1,0.01]],
      'neck': [0,0,30],
      'breast': [0,0,20],
      'belly': [0,0,-10] }],
    ['押し', {
      'belly': [0,0,-2],
      'shoulder': [[10,0.4], [10,0.4]],
      'hip': [[-50,0,0.05,0.15], [-50,0,0.05,0.15]] }],
    ['抜き', {
      'belly': [0,0,-40],
      'shoulder': [[-20,0.15], [-20,0.15]],
      'hip': [[-30,0,0.1,0.1], [-30,0,0.1,0.1]] }],
    ['離手', {
      'shoulder': [[0,0.3], [0,0.3]],
      'elbow': [[20,0.1], [20,0.1]],
      'hip': [[0,30,0.2,0.1], [0,30,0.2,0.1]],
      'neck': [0,0,20],
      'breast': [0,0,30],
      'belly': [0,0,20] }],
    ['離手', {
      'shoulder': [[90,0.3], [90,0.3]],
      'elbow': [[20,0.1], [20,0.1]],
      'hip': [[160,30,0.3,0.1], [160,30,0.3,0.1]],
      'neck': [0,0,20],
      'breast': [0,0,30],
      'belly': [0,0,20] }],
    ['押し(肩角度有り)',{
      'shoulder': [[10,0.2], [10,0.2]],
      'hip': [[10,0,0.3,0.2], [10,0,0.3,0.2]],
      'breast': [0,0,1],
      'belly': [0,0,-10] }],
    ['バーキャッチ', {}],
    ['押し', {}],
    ['閉脚浮腰', {}],
    ['背倒立', {
      'shoulder': [[60,0.2], [60,0.2]],
      'hip': [[0,0,0.2,0.2], [0,0,0.2,0.2]] }],
    ['押し', {'shoulder': [[5,0.2], [5,0.2]] }] ],
  '抱え込み宙返り降り': [
    ['押し', {}],
    ['抜き', {
      shoulder: [[-25, 0.1], [-25, 0.1]],
      hip: [[-20, 0, 0.15, 0.2], [-20, 0, 0.15, 0.2]] }],
    ['あふり', {
      shoulder: [[20, 0.2], [20, 0.2]],
      hip: [[25, 0, 0.25, 0.2], [25, 0, 0.25, 0.2]],
      neck: [0, 0, 3],
      breast: [0, 0, 10],
      belly: [0, 0, 5] }],
    ['離手',{
      shoulder: [[10, 0.2], [10, 0.2]],
      hip: [[10, 0, 0.3, 0.2], [10, 0, 0.3, 0.2]],
      neck: [0, 0, -15] }],
    ['抱え込み(弱)', {}],
    ['伸身',{
      shoulder: [[20, 0.2], [20, 0.2]],
      neck: [0, 0, -25] }],
    ['着地', {}] ],
  '伸身宙返り半捻り降り': [
    ['押し', {}],
    ['抜き', {
      shoulder: [[-25, 0.1], [-25, 0.1]],
      hip: [[-20, 0, 0.15, 0.2], [-20, 0, 0.15, 0.2]] }],
    ['あふり', {
      shoulder: [[20, 0.2], [20, 0.2]],
      hip: [[25, 0, 0.25, 0.2], [25, 0, 0.25, 0.2]],
      neck: [0, 0, 3],
      breast: [0, 0, 10],
      belly: [0, 0, 5] }],
    ['離手',{
      shoulder: [[10, 0.2], [10, 0.2]],
      hip: [[10, 0, 0.3, 0.2], [10, 0, 0.3, 0.2]],
      neck: [0, 0, -15] }],
    ['伸身',{
      shoulder: [[20, 0.2], [20, 0.2]],
      neck: [0, 0, -25] }],
    ['捻り', {}],
    ['着地', {}] ],
  '伸身ムーンサルト': [
    ['押し', {}],
    ['抜き', {}],
    ['押し',
     { 'shoulder': [[30,0.1], [30,0.1]],
       'hip': [[120,0,0.1,0.1], [120,0,0.1,0.1]],
       'neck': [0,0,-20],
       'breast': [0,0,20],
       'belly': [0,0,-10]}],
    ['閉脚浮腰', {'hip': [[80,0,0.1,0.1], [80,0,0.1,0.1]]}],
    ['押し', {'hip': [[10,0,0.01,0.3], [10,0,0.01,0.3]]}],
    ['抜き',
     {'shoulder': [[-15,0.2], [-10,0.1]],
      'hip': [[-10,0,0.15,0.3], [-10,0,0.15,0.3]]}],
    ['押し', {}],
    ['押し',
     {'shoulder': [[70,0.2], [70,0.3]],
      'hip': [[80,0,0.05,0.1], [80,0,0.05,0.1]],
      'neck': [0,0,-20],
      'breast': [0,0,40],
      'belly': [0,0,40]}],
    ['バーキャッチ', {'grip': ['catch','release']}],
    ['閉脚浮腰', {}],
    ['離手', {}],
    ['捻り',
     {'hip': [[30,0,0.2,0.2], [30,0,0.2,0.2]],
      'breast': [0,0,7],
      'belly': [0,0,2],
      'neck': [30,45,40]}],
    ['伸身',
     {'shoulder': [[240,0.1], [120,0.1]],
      'hip': [[-5,1,0.2,0.1], [-5,1,0.2,0.1]],
      'belly': [0,0,-10],
      'neck': [0,0,3]}],
    ['直線',
     {'neck': [0,0,-15],
      'shoulder': [[90,0.15], [90,0.15]],
      'breast': [0,0,15],
      'belly': [0,0,1],
      'hip': [[80,1,0.15,0.1], [80,1,0.15,0.1]],
      'knee': [[40,0.2],[40,0.2]]} ]],
  '行進': [
    ['伸身',
     { shoulder: [[240, 0.1], [120, 0.1]],
       neck: [0, 0, 3] }]],
  '捻り1': [
    ['捻り',
     { hip: [[10, 0, 0.2, 0.2], [10, 0, 0.2, 0.2]],
       breast: [0, 0, 7],
       belly: [0, 0, 2] }]],
  '捻り2': [
    ['捻り',
     { hip: [[10, 0, 0.2, 0.2], [10, 0, 0.2, 0.2]],
       breast: [0, 0, 7],
       belly: [0, 0, 2],
       neck: [30, 45, 40] }]],
  '捻り3': [
    ['捻り',
     { shoulder: [[170, 0.4], [220, 0.1]],
       elbow: [[120, 0.4], [120, 0.1]],
       hip: [[10, 0, 0.2, 0.2], [10, 0, 0.2, 0.2]],
       breast: [0, 0, 7],
       belly: [0, 0, 2] }]],
  '捻り4': [
    ['捻り',
     { shoulder: [[170, 0.4], [220, 0.1]],
       elbow: [[120, 0.4], [120, 0.1]],
       hip: [[10, 0, 0.2, 0.2], [10, 0, 0.2, 0.2]],
       breast: [0, 0, 7],
       belly: [0, 0, 2],
       neck: [30, 45, 40] }]],
  '捻り5': [
    ['捻り',
     { shoulder: [[40, 0.2], [220, 0.1]],
       elbow: [[120, 0.2], [120, 0.1]],
       hip: [[10, 0, 0.2, 0.2], [10, 0, 0.2, 0.2]],
       breast: [0, 0, 7],
       belly: [0, 0, 2] }]],
  '捻り6': [
    ['捻り',
     { shoulder: [[40, 0.2], [220, 0.1]],
       elbow: [[120, 0.2], [120, 0.1]],
       hip: [[10, 0, 0.2, 0.2], [10, 0, 0.2, 0.2]],
       breast: [0, 0, 7],
       belly: [0, 0, 2],
       neck: [30, 45, 40] }]]
};

export { params, dousa_dict, start_list, waza_list, waza_dict };
