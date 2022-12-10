'use strict';
import * as THREE from './js/three/build/three.module.js';
import { GUI } from './js/three/examples/jsm/libs/dat.gui.module.js';
import { TrackballControls } from
  './js/three/examples/jsm/controls/TrackballControls.js';
import { params, dousa_dict, start_list, waza_list, waza_dict } from
  './dataDevel.js';

/* x軸: 鉄棒の伸びている方向。初期配置の右手方向が +。
   y軸: 上下方向。上が +。
   z軸: 前後方向。後(手前)方向が +。*/

let debug = location.hash == '#debug';
let av; // デバッグ用矢印。

const rad_per_deg = Math.PI/180;
const L = 0;
const R = 1;

/* 詳細編集を使うと、start_list, waza_listに新しい技を追加出来る。
   追加された技か、元から用意された技かは、リスト中の要素番号を PREDEF_*_LEN
   と比較して区別する。 */
const PREDEF_START_LIST_LEN = start_list.length;
const PREDEF_WAZA_LIST_LEN = waza_list.length;

/* 調整可能なパラメーター */
const gui_params = {};

/* 色関係のパラメーターのキー */
const color_params_keys = ['肌の色',  '色1', '色2', '長パン'];

/* ページリロードした時の構成 */
const first_composition = ['後振り下し', '車輪', '車輪'];

/* デバッグ出力用クラス */
const DebugLog = {
  count: 0,
  freq: 0,

  reset: function() {},
  changeFreq: function() {},
  countUp: function() {},
  check_d: function() {},

  reset_d: function() {
    this.count = this.freq = 0;
  },

  changeFreq_d: function() {
    if ( this.freq == 0 )
      this.freq = 20;
    else
      this.freq >>= 1;
    console.log('DebugLog: ' + this.freq );
  },

  countUp_d: function() {
    this.count += 1;
    if ( this.count >= this.freq )
      this.count = 0;
  },

  check_d: function() {
    return this.count == this.freq - 1;
  }
};

if ( debug ) {
  DebugLog.reset = DebugLog.reset_d;
  DebugLog.changeFreq = DebugLog.changeFreq_d;
  DebugLog.countUp = DebugLog.countUp_d;
  DebugLog.check = DebugLog.check_d;
}

/* Ammo.btMatrix3x3 m をデバッグ用に表示する。 */
function showMat(m) {
  let s = [];
  for ( let i = 0; i < 3; ++i ) {
    let r = m.getRow(i);
    s.push(`[${[r.x(), r.y(), r.z()]}]`);
  }
  console.log(`[${s.join(',\n')}]`)
}

/* マウスイベントとタッチイベント両方が起きないようにする。
   タッチイベントが来たら、event.preventDefault()を出す、とか色々試したが、
   環境によって上手く行かず面倒臭くなったので、一回でもタッチイベントが来たら、
   それ以後はマウス関係のイベントは全部無視するようにした */
let touchScreenFlag = false;

let camera, scene, renderer, control;
let physicsWorld;
let clock = new THREE.Clock();
let dousa_clock = new THREE.Clock(); // 一つの動作当りの時間計測
let replayInfo = {  // 再生用情報置き場
  records: [],
  lastDousaPos: 0,
  replayPos: 0,
  remainingDelta: 0
};

let transformAux1;
let rigidBodies = [];

/* state:
     main: 全体状態 'reset', 'init', 'settings', 'run', 'replay', 'pause'
       (pauseはデバッグモード専用)。
     saved_main: pauseしてる時、pause前の状態。
     entry_num: 登録した技の幾つ目を実行中か。
     waza_pos: 技の幾つ目の動作を実行中か。
     active_key: 最後に押したキーのkeycode, 13, 32, null('init'の時)。
     landing:  着地状態。
               0: 床に両足触れてない, 1: 左足が触れてる, 2: 右足, 3:両足触れてる,
               -1: 着地成功, -2: 着地失敗。
 */
let state;

let bar, floor;
let bar_curve, bar_mesh; // バーのスプライン表示用
let bar_spring; // バーの弾性
let pole_object; // 物理的実体無し。表示のみ。

let gymnast = {
  body: { // 要素は Ammo.btRigidBody
    pelvis: null,
    spine: null,
    chest: null,
    head: null,
    upper_leg: [null, null], // [left_part, right_part]。左右あるパーツは他も同様。
    lower_leg: [null, null],
    upper_arm: [null, null],
    lower_arm: [null, null]
  },

  joint: {
    belly: null,
    breast: null,
    neck: null,
    hip: [null, null],
    knee: [null, null],
    shoulder: [null, null],      // hinge肩
    shoulder6dof: [null, null],  // 3自由度のある肩
    elbow: [null, null],
    landing: [null, null],       // 着地用。upsideDown()の中で作る。
    grip: [null, null],
    grip_switchst: [null, null], // スイッチスタンス(ツイストした時)のグリップ
  },

  motor: {
    hip: [null, null],
    grip: [null, null],
    grip_switchst: [null, null]
  },

  body_parts: [],    // bodyの全要素
  air_res_parts: [], // 着地の時空気抵抗を受けるbodyの要素

  is_switchst: false,          // スイッチスタンスか
  shoulder_winding: [0, 0],    // 肩の角度の巻き付き回数(左右)。離手するとリセット
  last_shoulder_angle: [0, 0], // 前回の肩の角度(-pi .. pi)
  is_hinge_shoulder: [true, true] // 左右の肩のジョイントがhingeか。
};

let helper_joint;

let curr_dousa = {};
let composition_by_num = []; // 構成を技番号の列で表現

function init() {
  initGUI();
  initData(); // gui_paramsを使うので、initGUI()を先にやらないといけない。
  initInput();
  initButtons();
  initGraphics();
  initPhysics();
  createObjects();
  showComposition();
}

function initData() {
  initStorage();

  for ( let i = 0; i < first_composition.length; ++i ) {
    let list = get_start_or_waza_list(i);
    composition_by_num.push(list.indexOf(first_composition[i]));
  }
}

function setWazaDict(name, seq) {
  /* waza_dict[name] を seq にする。

     seqの中に、肩6DoFの 4成分指定が入っていれば 6成分指定に書き直す。
     4成分指定は無しにしたいが、既に利用されてしまっている。
     6成分指定も、要素の順番が x,z,y でややこしく、腰などの要素の順と違うのが嫌。*/
  for ( let dousa of seq ) {
    if ( !('shoulder' in (dousa[1] || {})) )
      continue;
    for ( let elem of dousa[1]['shoulder'] ) {
      if ( elem.length == 4 ) {
        elem.splice(2, 0, 0);
        elem.push(0.1);
      }
    }
  }

  waza_dict[name] = seq;
}

function initStorage() {
  function unique_name(name, list) {
    /* バージョンアップでユーザー定義していた技と同名の技が公式版に追加された場合のケア。
       元のユーザー定義の技名の後に '_'を追加して、削除したり名前を変えられる様にする。
       一つ以上の'_'で終わる技をユーザーが登録しているかも知れないので注意。*/
    while ( list.indexOf(name) >= 0 )
      name += '_';
    return name;
  }

  let storage = localStorage.getItem('HighBar');
  let need_update = false;

  if ( storage === null ) {
    storage = {
      user_start_list: [],
      user_waza_list: [],
      colors: {}
    };
    localStorage.setItem('HighBar', JSON.stringify(storage));
  } else {
    storage = JSON.parse(storage);
    if ( !('colors' in storage) ) {
      // colors の項目は新しい版から追加された。
      need_update = true;
      storage['colors'] = {};
    }
  }

  for ( let [i, user] of [[0, 'user_start_list'], [1, 'user_waza_list']] ) {
    for ( let item of storage[user] ) {
      let list = get_start_or_waza_list(i),
          waza = unique_name(item.waza, list),
          seq = item.seq;
      need_update |= (waza != item.waza);
      list.push(waza);
      setWazaDict(waza, seq);
    }
  }

  for ( let item in storage.colors )
    gui_params[item] = storage.colors[item];

  if ( need_update )
    updateStorage();
}

function initGUI() {
  function resetParam() {
    for ( key in params.adjustable )
      gui_params[key] = params.adjustable[key][0];
  }

  let gui = new GUI({ autoPlace: false }),
      folder1 = gui.addFolder('力の調整'),
      folder2 = gui.addFolder('その他'),
      folder3 = gui.addFolder('色'),
      key;

  resetParam();
  for ( key of ['首の力', '肩の力', '胸の力', '腹の力', '肘の力', '膝の力',
                '屈身にする時間', '腰の力の最大値', '手首の力の最大値'] )
    folder1.add(gui_params, key, ...params.adjustable[key][1]).listen();
  for ( key of ['時間の流れ', 'キャッチ時間', 'キャッチ幅',
                '着地空気抵抗', '着地補助範囲',
                'バー弾性', 'バー減衰', 'マット摩擦'] )
    folder2.add(gui_params, key, ...params.adjustable[key][1]).listen();

  for ( key of ['肌の色',  '色1', '色2'])
    folder3.addColor(gui_params, key).listen();
  folder3.add(gui_params, '長パン').listen();

  gui_params['初期値にリセット'] =
    function() { if ( confirm() ) resetParam(); };
  gui.add(gui_params, '初期値にリセット');

  document.getElementById('gui').appendChild(gui.domElement);
}

function setColors() {
  let skin_color = gui_params['肌の色'],
      color1 = gui_params['色1'],
      color2 = gui_params['色2'],
      leg_color =  gui_params['長パン'] ? color2 : skin_color,
      obj;

  for ( let x of gymnast.body.upper_arm.concat(gymnast.body.lower_arm) )
    x.three.material.color.set(skin_color);
  obj = gymnast.body.head.three.children[0];
  obj.material.color.set(skin_color);

  for ( let x of [gymnast.body.spine, gymnast.body.chest] )
    x.three.material.color.set(color1);

  gymnast.body.pelvis.three.material.color.set(color2);

  /* 足の色を短パン、長パンに合うように決める。

     指摘があるまで、鉄棒なのに短パンを履いていた。恥ずかしい。
     各種の説明動画などを作り直したり、色が違っていると断りを入れるのは大変なので、
     デフォルトでは短パンを履いたままにして、
     GUIで指定した時だけ長パンを履くようにして誤魔化すことにした。 */
  for ( let x of gymnast.body.upper_leg.concat(gymnast.body.lower_leg) )
    x.three.material.color.set(leg_color);

  updateStorage(); // 修正が無くても毎回呼ぶが気にしない。
}

function setAdjustableForces() {
  params.max_force.hip[0] = gui_params['腰の力の最大値'];
  dousa_dict['屈身(弱)']['hip'][0][2] =
    dousa_dict['屈身(弱)']['hip'][1][2] =
    dousa_dict['屈身(強)']['hip'][0][2] =
    dousa_dict['屈身(強)']['hip'][1][2] = gui_params['屈身にする時間'];
  setHipMaxMotorForce(...params.max_force.hip);

  gymnast.joint.neck.setMaxMotorImpulse(gui_params['首の力']);
  gymnast.joint.breast.setMaxMotorImpulse(gui_params['胸の力']);
  gymnast.joint.belly.setMaxMotorImpulse(gui_params['腹の力']);

  let shoulder_impulse = gui_params['肩の力'],
      elbow_impulse = gui_params['肘の力'],
      knee_impulse = gui_params['膝の力'],
      grip_max_force = gui_params['手首の力の最大値'];

  for ( let lr = L; lr <= R; ++lr ) {
    /* bulletのソースから多分、
       btHingeConstraint.enableAngularMotor() の maxMotorImpulse と
       btGeneric6DofConstraint の rotationLimitMotor の maxMotorForce は、
       maxMotorFoce / fps = maxMotorImpulse
       の関係にあると思う。
       但し、fpsは physicsWorld.stepSimulation() の fixedTimeStep 。

       rotationLimitMotor の maxLimitForceは?
    */
    gymnast.joint.shoulder[lr].enableAngularMotor(
      gymnast.is_hinge_shoulder[lr], 0, shoulder_impulse);
    for ( let xyz = 0; xyz < 3; ++xyz ) {
      let motor = gymnast.joint.shoulder6dof[lr].getRotationalLimitMotor(xyz);
      motor.m_maxMotorForce = shoulder_impulse * params.fps;
      motor.m_enableMotor = !gymnast.is_hinge_shoulder[lr];
    }

    gymnast.joint.elbow[lr].enableAngularMotor(true, 0, elbow_impulse);
    gymnast.joint.knee[lr].enableAngularMotor(true, 0, knee_impulse);
  }
  setGripMaxMotorForce(grip_max_force, params.max_force.grip[1]);

  let spring = gui_params['バー弾性'] * 1e+4,
      damping = gui_params['バー減衰'] * 1e-6;
  bar_spring.setStiffness(1, spring);
  bar_spring.setDamping(1, damping);
  bar_spring.setStiffness(2, spring);
  bar_spring.setDamping(2, damping);

  let friction = gui_params['マット摩擦'];
  floor.setFriction(friction);
  floor.setRollingFriction(friction);
}

function setCurJointShoulder(lr, is_hinge) {
  gymnast.is_hinge_shoulder[lr] = is_hinge;
  if ( state == null || state.main == 'init' ) {
    // 初期状態では6Dofも有効にしないと、リセット前の6Dofの状態が残ってしまう。
    gymnast.joint.shoulder6dof[lr].setEnabled(true);
  } else {
    gymnast.joint.shoulder6dof[lr].setEnabled(!is_hinge);
  }
  gymnast.joint.shoulder[lr].setEnabled(is_hinge);
  for ( let i = 0; i < 3; ++i )
    gymnast.joint.shoulder6dof[lr].getRotationalLimitMotor(i)
    .m_enableMotor = !is_hinge;
}

function checkCurJointShoulder(prev_shoulder, cur_shoulder) {
  if ( prev_shoulder == null || cur_shoulder == null )
    return;

  for ( let lr = L; lr <= R; ++lr ) {
    let is_prev_hinge = prev_shoulder[lr].length == 2;
    let is_cur_hinge = cur_shoulder[lr].length == 2;
    if ( is_prev_hinge != is_cur_hinge ) {
      setCurJointShoulder(lr, is_cur_hinge);

      /* 肩6DoFでy軸回りの回転指定のある時だけ、グリップのy軸回転に制限を付ける。

         これをやらないと、片手でバーを握ってる時に折角肩をy軸回転させても、
         吊り輪の環みたいにグリップの所で回転が起きて効果が打ち消されてしまう。

         また、つねにグリップのy軸回転を制限していると、今度は移行で逆手になったりした時、
         握り変えが必要になったり、順手車輪と逆手車輪などを別の技にしないといけなくなり、
         色々と面倒。*/
      let lower, upper;
      if ( is_cur_hinge || cur_shoulder[lr][2] == 0 ) {
        lower = params.flexibility.grip.angle_min;
        upper = params.flexibility.grip.angle_max;
      } else {
        lower = params.flexibility.grip.angle_min2;
        upper = params.flexibility.grip.angle_max2;
      }
      gymnast.joint.grip[lr].setAngularLowerLimit(
        new Ammo.btVector3(...to_rads(lower)));
      gymnast.joint.grip[lr].setAngularUpperLimit(
        new Ammo.btVector3(...to_rads(upper)));
      gymnast.joint.grip_switchst[lr].setAngularLowerLimit(
        new Ammo.btVector3(...to_rads(lower)));
      gymnast.joint.grip_switchst[lr].setAngularUpperLimit(
        new Ammo.btVector3(...to_rads(upper)));
    }
  }
}

function updown(ev) {
  let key = ev.keyCode;
  if ( state.main == 'settings' ) {
    return;
  } else if ( state.main == 'init' ) {
    state = {
      main: 'run', entry_num: 1, waza_pos: 0, active_key: key, landing: 0 };
    changeButtonSettings();
    for ( let blur of document.querySelectorAll('.blur')) {
      blur.blur();
    }

    setAdjustableForces();
    enableHelper(false);
    startRecording();
  } else {
    if ( key != state.active_key ) {
      state.active_key = key;
      if ( state.entry_num
           < document.querySelectorAll('select.waza').length ) {
        state.entry_num += 1;
        state.waza_pos = 0;
      } else {
        /* 構成の最後まで進んだら、キーを入れ替えの効果は無しにする。
           これを省くと、再生時に構成の最後以降、activeキーの表示が
           おかしくなる */
        let waza = current_waza(),
            waza_seq = waza_dict[waza];
        if ( ++state.waza_pos >= waza_seq.length )
          state.waza_pos = (waza_seq[waza_seq.length-1][0] != '着地')
          ? 0 : waza_seq.length - 1;
      }
    } else {
      let waza = current_waza(),
          waza_seq = waza_dict[waza];
      if ( ++state.waza_pos >= waza_seq.length )
        state.waza_pos = (waza_seq[waza_seq.length-1][0] != '着地')
        ? 0 : waza_seq.length - 1;
    }
  }

  let d = waza_dict[current_waza()][state.waza_pos],
      next_dousa = dousa_dict[d[0]],
      variation = d[1] || {}, // バリエーションを指定出来るようにしてみる
      prev_shoulder = curr_dousa['shoulder']; // 二種類の肩関節の使い分け
  for ( let x in next_dousa )
    curr_dousa[x] = next_dousa[x];
  for ( let x in variation )
    curr_dousa[x] = variation[x];

  checkCurJointShoulder(prev_shoulder, curr_dousa['shoulder']);

  showActiveWaza();
  addDousaRecord(curr_dousa);
  dousa_clock.start();
}

function keydown(ev) {
  if ( state.main == 'settings' || state.main == 'replay' )
    return;

  let key = ev.keyCode == 32 ? 'space' : 'enter';
  document.querySelector('button#' + key).classList.toggle('active', true);
  if ( ev.keyCode == state.active_key && state.waza_pos % 2 == 0 )
    return;

  updown(ev);
  addKeyRecord(ev.keyCode); // updown()からstartRecording()が呼ばれる事に注意
}

function keyup(ev) {
  if ( state.main == 'settings' || state.main == 'replay' )
    return;

  let key = ev.keyCode == 32 ? 'space' : 'enter';
  document.querySelector('button#' + key).classList.toggle('active', false);
  if ( state.waza_pos % 2 == 1 )
    return;

  /* space押したまま、enterを押して技を変えて、それからspaceを放す時に
     反応させない */
  if ( ev.keyCode == state.active_key ) {
    updown(ev);
  }
  addKeyRecord(ev.keyCode | 0x100);
}

function keyevent(ev) {
  switch ( ev.keyCode ) {
  case 32: // ' ':
  case 13: // Enter
    if ( ev.type == 'keydown' )
      keydown(ev);
    else if ( ev.type == 'keyup' )
      keyup(ev);
    break;
  case 82: // 'R'
  case 114: // 'r'
    if ( state.main == 'run' || state.main == 'replay' ) {
      doReset();
      DebugLog.reset();
    }
    break;
  case 80: // 'P'
  case 112: // 'p'
    // 色々な状態で正しく動作するか確認してないので、デバッグモード専用。
    if ( !debug )
      break;
    if ( ev.type != 'keydown' )
      break;
    if ( state.main == 'pause' ) {
      state.main = state.saved_main;
      clock.start();
    } else {
      state.saved_main = state.main;
      state.main ='pause';
      clock.stop();
    }
    break;
  case 76: // 'L'
  case 108: // 'l'
    if ( ev.type == 'keydown' )
      DebugLog.changeFreq();
    break;
  default:
    break;
  }
}

function initInput() {
  window.addEventListener('keydown', keyevent, false);
  window.addEventListener('keyup', keyevent, false);
  for ( let move of document.querySelectorAll('button.move') ) {
    move.addEventListener('mousedown', function(ev) {
      if ( touchScreenFlag )
        return;
      ev.keyCode = ev.target.getAttribute('id') == 'space' ? 32 : 20;
      keydown(ev);
    }, false);
    move.addEventListener('mouseup', function(ev) {
      if ( touchScreenFlag )
        return;
      ev.keyCode = ev.target.getAttribute('id') == 'space' ? 32 : 20;
      keyup(ev);
    }, false);
    // mousedownのまま、ボタンの外に出てしまった時対応
    move.addEventListener('mouseout', function(ev) {
      if ( touchScreenFlag )
        return;
      ev.keyCode = ev.target.getAttribute('id') == 'space' ? 32 : 20;
      if ( state.main == 'run' )
        keyup(ev);
    }, false);
    // ボタンの外でmousedownのまま、ボタンの中に入ってきた時対応
    move.addEventListener('mouseenter', function(ev) {
      if ( touchScreenFlag )
        return;
      ev.keyCode = ev.target.getAttribute('id') == 'space' ? 32 : 20;
      if ( state.main == 'run' )
        keydown(ev);
    }, false);
    move.addEventListener('touchstart', function(ev) {
      touchScreenFlag = true;
      ev.keyCode = ev.target.getAttribute('id') == 'space' ? 32 : 20;
      keydown(ev);
    }, false);
    move.addEventListener('touchend', function(ev) {
      touchScreenFlag = true;
      ev.keyCode = ev.target.getAttribute('id') == 'space' ? 32 : 20;
      keyup(ev);
    }, false);
  }
}

function initButtons() {
  document.getElementById('reset').addEventListener('click', doReset, false);
  document.getElementById('replay').addEventListener('click', doReplay, false);

  makeWazaSelector();

  document.querySelector('#composition').addEventListener('click', function() {
    document.querySelector('#settings').style.visibility = 'visible';
    state.main = 'settings';
  }, false);

  document.querySelector('#pole-check').addEventListener('change', function() {
    let elem = document.querySelector('#pole-check');
    pole_object.visible = elem.checked;
    // チェックしてアクティブになった以後のスペースキーに反応してしまうのを避ける。
    elem.blur();
  });

  document.querySelector('#settings-ok').addEventListener('click', function() {
    setColors();

    replayInfo.records = [];

    document.querySelector('#settings').style.visibility = 'hidden';
    composition_by_num = [];
    for ( let elem of document.querySelectorAll('.initialize') )
      composition_by_num.push(elem.selectedIndex);
    showComposition();
    state.main = 'init';
    doResetMain();
  }, false);

  document.querySelector('#plus').addEventListener('click', plus, false);
  document.querySelector('#minus').addEventListener('click', minus, false);
  for ( let button of document.querySelectorAll('.edit') )
    button.addEventListener('click', showEdit, false);

  document.querySelector('#textcode-ok').addEventListener('click', function() {
    try {
      let parsed = JSON.parse(
        document.querySelector('#textcode-area').value);
      checkParsed(parsed);
    } catch (error) {
      alertError(error);
      return;
    }

    hideEdit();
    if ( parsed.detail !== undefined )
      parsed.detail = registerWaza(parsed.detail); // ユーザー定義技の追加と削除
    restoreParsed(parsed);
  }, false);

  document.querySelector('#textcode-cancel').addEventListener(
    'click', hideEdit, false);
}

function alertError(error) {
  if ( error instanceof SyntaxError ) {
    /* jsonlint https://github.com/zaach/jsonlint/blob/master/web/jsonlint.js
       を使うと間違った所を教えてくれるらしいが。 */
    alert('記述に間違いがあります。');
    return
  }

  if ( typeof(error) == 'string' ) {
    alert(error);
    return;
  }

  let str = ( 'dousa' in error )
      ? `技名 ${error.waza} 、${error.dousa} 内に間違いがあります。`
      :  `技名 ${error.waza} 内に間違いがあります。`;
  if ( error.message )
    str += ': ' + error.message;
  alert(str);
}

function showEdit() {
  document.querySelector('#settings').style.visibility = 'hidden';
  document.querySelector('#textcode').style.visibility = 'visible';

  let obj = this.hasAttribute('detail') ? detailObj() : briefObj();
  document.querySelector('#textcode-area').value =
    JSON.stringify(obj , null, 2);
}

function getParams() {
  // gui_paramsの内、色関係はlocalStorageに保存するので、編集項目からは外す。
  let cp_params = Object.assign({}, gui_params);
  for ( let key of color_params_keys )
    delete cp_params[key]

  return cp_params;
}

function detailObj() {
  let detail = [];
  for ( let elem of document.querySelectorAll('.initialize') ) {
    let waza = elem.selectedOptions[0].textContent,
        seq = waza_dict[waza];
    detail.push({waza: waza, seq: seq});
  }

  return {params: getParams(), detail: detail};
}

function briefObj() {
  let composition = [];
  for ( let elem of document.querySelectorAll('.initialize') )
    composition.push(elem.selectedOptions[0].textContent);
  return {params: getParams(), composition: composition};
}

function hideEdit() {
  document.querySelector('#textcode').style.visibility = 'hidden';
  document.querySelector('#settings').style.visibility = 'visible';
}

function checkParsed(parsed) {
  if ( !('params' in parsed) )
    throw '"params"の指定がありません。'
  if ( 'composition' in parsed )
    checkComposition(parsed['composition']);
  else if ( 'detail' in parsed )
    checkDetail(parsed['detail']);
  else
    throw '"composition"または"detail"の指定がありません。'
}

function checkComposition(comps) {
  if ( !Array.isArray(comps) )
    throw SyntaxError();
  if ( comps.length <= 1 )
    throw '構成には最低、初期動作と、それ以外の技一つを入れなくてはいけません。';

  for ( let i = 0; i < comps.length; i++ ) {
    let comp = comps[i];
    if ( !strCheck(comp) )
      throw '技名がありません。';

    let list = (i==0 ? start_list : waza_list);
    if ( !list.includes(comp) )
      throw '技名 ' + comp + ' という技は登録されていません。';
  }
}

function checkDetail(detail) {
  if ( !Array.isArray(detail) )
    throw SyntaxError();
  if ( detail.length <= 1 )
    throw '構成には最低、初期動作と、それ以外の技一つを入れなくてはいけません。';

  for ( let i = 0; i < detail.length; ++i ) {
    let di = detail[i];
    if ( !(di instanceof Object) )
      throw SyntaxError();
    let [comp, seq] = [di.waza, di.seq];
    if ( !strCheck(comp) )
       throw '技名がありません。';
    if ( !Array.isArray(seq) )
      throw '技を構成する動作指定がありません。';
    let list = get_start_or_waza_list(i),
        predef_len = get_predef_len(i);
    let index = list.indexOf(comp);
    if ( 0 <= index && index < predef_len) {
      if ( JSON.stringify(seq) != JSON.stringify(waza_dict[comp]) )
          throw `技名 ${comp} が書き換えられています。`;
    } else { // 追加された技
      // seq.length == 0 でもエラーにしない。その時は、その技があれば削除する。
      if ( i == 0 && seq.length > 1 )
        throw '開始姿勢は一つしか指定出来ません。';
      try {
        checkSequence(seq, i);
      } catch (error) {
        error.waza = comp;
        throw error;
      }
    }
  }
}

function checkSequence(seq, waza_i) {
  for ( let seq_i = 0; seq_i < seq.length; ++seq_i ) {
    let dousa = seq[seq_i];
    if ( !Array.isArray(dousa) ||
         dousa.length != 2 ||
         !strCheck(dousa[0]) ||
         !(dousa[1] instanceof Object) )
      throw Error('動作名か調整指定がありません。');

    let [dousa_name, adjustment] = dousa;
    try {
      if ( !(dousa_name in dousa_dict) )
        throw Error('登録されていない動作です。');
      checkAdjustment(adjustment, waza_i);
    } catch (error) {
      error.dousa = `${seq_i + 1}個目の動作 ${dousa_name}`;
      throw error;
    }
  }
}

const checkFuncTable = {
  shoulder: shoulderCheck,
  hip: hipCheck,
  neck: neckCheck,
  breast: breastCheck,
  belly: bellyCheck,
  knee: kneeCheck,
  elbow: elbowCheck,
  grip: gripCheck };

function checkAdjustment(adjustment, waza_i) {
  if ( waza_i == 0 &&
       (!('angle' in adjustment) || typeof(adjustment['angle']) != 'number') )
    throw Error('開始姿勢にはangleを指定する必用があります。');

  for ( let key in adjustment ) {
    let value = adjustment[key];
    let checkFunc = checkFuncTable[key];
    if ( checkFunc == undefined )
      continue; // エラーにしない。コメントとか用。'landing'もここでスルー。
    try {
      if ( !Array.isArray(value) )
        throw Error();
      checkFunc(value);
    } catch (error) {
      throw Error(`調整指定${key}内。`);
    }
  }
}

function shoulderCheck(value) {
  arrayCheck(value, 2, 'array');

  // 肩の角度の指定方法は三通りある。
  for ( let v of value ) {
    if ( v.length == 2 )
      arrayCheck(v, 2, 'number'); // 従来のヒンジ自由度しかない2要素指定
    else if ( v.length == 4 )
      arrayCheck(v, 4, 'number'); // 肩角度、肩を横に開く角度を指定
    else
      arrayCheck(v, 6, 'number'); // 全3自由度を持った新しい6要素指定
  }
}

function hipCheck(value) {
  arrayCheck(value, 2, 'array');
  for ( let v of value )
    arrayCheck(v, 4, 'number');
}

function neckCheck(value) {
  coneCheck(value);
}

function breastCheck(value) {
  coneCheck(value);
}

function bellyCheck(value) {
  coneCheck(value);
}

function kneeCheck(value) {
  arrayCheck(value, 2, 'array');
  for ( let v of value )
    arrayCheck(v, 2, 'number');
}

function elbowCheck(value) {
  arrayCheck(value, 2, 'array');
  for ( let v of value )
    arrayCheck(v, 2, 'number');
}

function gripCheck(value) {
  arrayCheck(value, 2, 'grip'); // 特例
}

function coneCheck(value) {
  arrayCheck(value, 3, 'number');
}

function arrayCheck(value, len, elem_type) {
  if ( value.length != len )
    throw Error();

  for ( let e of value ) {
    switch ( elem_type ) {
    case 'array':
      if ( !Array.isArray(e) )
        throw Error();
      break;
    case 'grip':
      if ( typeof(e) == 'string' && ['catch', 'release'].includes(e) )
        break;
      arrayCheck(e, 4, 'number');
      break;
    default:
      if ( typeof(e) != elem_type )
        throw Error();
      return;
    }
  }
}

function strCheck(value) {
  return typeof(value) == 'string' && value != '';
}

function registerWaza(detail) {
  let newDetail = [];
  let list, predef_len;
  let changed = false;

  for ( let i = 0; i < detail.length; ++i ) {
    let d = detail[i],
        [comp, seq] = [d.waza, d.seq];
    list = get_start_or_waza_list(i);
    predef_len = get_predef_len(i);
    let index = list.indexOf(comp);
    if ( 0 <= index && index < predef_len ||
         JSON.stringify(seq) == JSON.stringify(waza_dict[comp]) ) {
      newDetail.push(d);
      continue;
    }

    changed = true;
    if ( seq.length == 0 ) {
      // seqが空の時は技を取り除く。分かりにくい仕様か。
      if ( index >= 0 ) {
        delete waza_dict[comp];
        list.splice(index, 1);

        // 消した穴はデフォルトで埋める。
        let waza = (i == 0) ? '後振り下し' : '車輪';
        newDetail.push({waza: waza, seq: waza_dict[waza]})
      }
    } else {
      if ( index < 0 )
        list.push(comp);
      setWazaDict(comp, seq);
      newDetail.push(d);
    }
  }

  if ( changed ) {
    updateStorage();
  }

  return newDetail;
}

function updateStorage() {
  let user_start_list = [],
      user_waza_list = [],
      colors = {};
  for ( let i = PREDEF_START_LIST_LEN; i < start_list.length; ++i ) {
    let waza = start_list[i];
    user_start_list.push({waza: waza, seq: waza_dict[waza]});
  }
  for ( let i = PREDEF_WAZA_LIST_LEN; i < waza_list.length; ++i ) {
    let waza = waza_list[i];
    user_waza_list.push({waza: waza, seq: waza_dict[waza]});
  }
  for ( let key of color_params_keys )
    colors[key] = gui_params[key];

  let storage = {
    user_start_list: user_start_list,
    user_waza_list: user_waza_list,
    colors: colors
  };
  localStorage.setItem('HighBar', JSON.stringify(storage));
}

function restoreParsed(parsed) {
  for ( let key in gui_params )
    if ( key in parsed['params'] )
      gui_params[key] = parsed['params'][key];

  let comps;
  if ( 'composition' in parsed ) {
    comps = parsed['composition'];
  } else {
    comps = [];
    for ( let d of parsed['detail'] )
      comps.push(d.waza);
  }

  composition_by_num = [];
  for ( let i = 0; i < comps.length; ++i ) {
    let list = get_start_or_waza_list(i);
    composition_by_num.push(list.indexOf(comps[i])); // index >= 0 はチェック済み
  }

  makeWazaSelector();
  let selects = document.querySelectorAll('#settings-list select');
  for ( let i = 0; i < composition_by_num.length; ++i ) {
    selects[i].selectedIndex = composition_by_num[i];
  }
}

function makeWazaSelector() {
  let len = document.querySelectorAll('select.waza').length;
  for ( let i = 1; i < len; ++i )
    minus();

  makeOptions(document.querySelector('#start-pos'), start_list);
  makeOptions(document.querySelector('select.waza'), waza_list);

  for ( let i = 2; i < composition_by_num.length; ++i )
    plus();
}

function makeOptions(sel, list) {
  while (sel.firstChild)
    sel.removeChild(sel.firstChild);

  for ( let waza of list ) {
    let option = document.createElement('option');
    option.textContent = waza;
    sel.appendChild(option);
  }
}

function plus() {
  let clone = document.querySelector('select.waza').cloneNode(true);
  document.getElementById('settings-list').insertBefore(
    clone, document.getElementById('plusminus'));
  document.getElementById('minus').removeAttribute('disabled');
}

function minus() {
  let selects = document.querySelectorAll('select.waza');
  if ( selects.length <= 1 )
    return; // 予備
  else if ( selects.length <= 2 )
    document.getElementById('minus').setAttribute('disabled', true);
  document.getElementById('settings-list').removeChild(
    selects[selects.length-1]);
}

function get_start_or_waza_list(entry_num) {
  return (entry_num == 0) ? start_list : waza_list;
}

function get_predef_len(entry_num) {
  return (entry_num == 0) ? PREDEF_START_LIST_LEN : PREDEF_WAZA_LIST_LEN;
}

function showComposition() {
  let list = document.getElementById('right-list');
  for ( let elem of document.querySelectorAll('#right-list>div') )
    elem.remove();
  for ( let i = 0; i < composition_by_num.length; ++i ) {
    let div = document.createElement('div');
    let waza_list = get_start_or_waza_list(i);
    div.appendChild(
      document.createTextNode(waza_list[composition_by_num[i]]));
    list.append(div);
  }
}

function showActiveWaza() {
  let w = document.querySelectorAll('#right-list>div');
  for ( let i = 0; i < w.length; ++i )
    w[i].classList.toggle('active', i == state.entry_num);
  w[state.entry_num].scrollIntoView(false);
}

function initGraphics() {
  let container = document.getElementById('container');
  camera = new THREE.PerspectiveCamera(
    60, container.offsetWidth / container.offsetHeight, 0.2, 2000);
  camera.position.set(7, 0, 3);
  scene = new THREE.Scene();
  scene.background = new THREE.Color(0xbfd1e5);
  renderer = new THREE.WebGLRenderer();
  renderer.setPixelRatio(window.devicePixelRatio);
  renderer.setSize(container.offsetWidth, container.offsetHeight);
  renderer.shadowMap.enabled = true;
  container.appendChild(renderer.domElement);

  scene.add(new THREE.AmbientLight(0x707070));

  if ( debug ) {
    av = [0,1,2].map(xyz => new THREE.ArrowHelper(
      new THREE.Vector3(1,0,0), new THREE.Vector3(0,0,0),2,
      [0xff0000, 0x00ff00, 0x0000ff][xyz]));
    for ( let xyz=0; xyz < 3; ++xyz)
      scene.add(av[xyz]);
  }

  let light = new THREE.DirectionalLight(0x888888, 1);
  light.position.set(3, 8, 0);
  scene.add(light);

  control = new TrackballControls(camera, container);
  control.target.setY(-2.7);
  control.rotateSpeed = 1.0;
  control.zoomSpeed = 1.2;
  control.panSpeed = 0.8;
  control.noZoom = false;
  control.noPan = false;
  control.staticMoving = true;
  control.dynamicDampingFactor = 0.3;
  // カメラの位置を変えても controlが上書きするので、こちらを変える。
  // 行儀良くないかも。
  control.target.set(0, -1., 0);
  control.enabled = true;

  window.addEventListener('resize', onWindowResize, false);
}

function initPhysics() {
  let collisionConfiguration = new Ammo.btDefaultCollisionConfiguration();
  let dispatcher = new Ammo.btCollisionDispatcher(collisionConfiguration);
  let broadphase = new Ammo.btDbvtBroadphase();
  let solver = new Ammo.btSequentialImpulseConstraintSolver();
  physicsWorld = new Ammo.btDiscreteDynamicsWorld(
    dispatcher, broadphase, solver, collisionConfiguration);
  physicsWorld.setGravity(new Ammo.btVector3(0, -9.8, 0));
  transformAux1 = new Ammo.btTransform();
}

function createObjects() {
  let [bar_r, bar_l, bar_h] = params.bar.size;
  let pole_r = params.pole.size;
  let [wire_x, wire_y, wire_z] = [
    params.wire.dist_x, params.wire.middle_y_from_top, params.wire.dist_z];
  let [floor_x, floor_y, floor_z] = params.floor.size; // 一辺の1/2
  let pelvis_r2 = params.pelvis.size[1];
  let spine_r2 = params.spine.size[1], spine_m = 0.13;
  let [chest_r1, chest_r2] = params.chest.size; // chest_r3は他では使わない
  let head_r2 = params.head.size[1];
  let upper_leg_h = params.upper_leg.size[1], upper_leg_x = params.upper_leg.x;
  let [lower_leg_r, lower_leg_h] = params.lower_leg.size,
      lower_leg_x = params.lower_leg.x;
  let [upper_arm_r, upper_arm_h] = params.upper_arm.size;
  let lower_arm_h = params.lower_arm.size[1];

  let body = gymnast.body,
      joint = gymnast.joint,
      motor = gymnast.motor;

  function resizeParams() {
    let scale = params.scale;
    bar_r *= scale; bar_l *= scale; bar_h *= scale
    floor_x *= scale; floor_z *= scale; // yも変えてもいいが
    // barの重さも scale^3 したいが、それをやると弾性なども変えないといかんのでやめる

    pole_r *= scale;
    wire_x *= scale; wire_y *= scale; wire_z *= scale;
  }

  function createShoulderJoint() {
    /* 肩は、HingeConstrと 6DofSpring2Constrの二つのモーター付きジョイントで固定し、
       動作によってどちらか一方のモーターのみを利用する。

       これは、従来、HingeConstrのみで固定していて、各技、各動作のパラメーターを
       そちら用に調整していて、新しく自由度を増やした 6DofConstr用に
       調整し直すのが難しいため。 */
    for ( let lr = L; lr <= R; ++lr ) {
      let sign = (lr == L ? -1 : +1);
      joint.shoulder[lr] = createHinge(
        body.chest, [sign * chest_r1, chest_r2, 0], null,
        body.upper_arm[lr], [-sign * upper_arm_r, -upper_arm_h/2, 0],
        null, null);

      joint.shoulder6dof[lr] = create6Dof(
        body.chest, [sign * chest_r1, chest_r2, 0], null,
        body.upper_arm[lr], [-sign * upper_arm_r, -upper_arm_h/2, 0], null,
        [params.flexibility.shoulder.shift_min,
         params.flexibility.shoulder.shift_max,
         params.flexibility.shoulder.angle_min,
         params.flexibility.shoulder.angle_max],
        null, Ammo.RO_YZX); // btGeneric6DofSpring2Constraint
    }
  }

  resizeParams();

  /* Three.jsの CylinderはY軸に沿った物しか用意されてない。
     X軸に沿うように回転させると、Bulletの方にまでその回転が反映されてしまい
     座標変換がややこしくなるので、画面に見えるバーとBulletに対応付けるバーを
     分けて扱う、という小細工をする。
     物理的なバーはただの円柱。画面に見えるバーはしなっているように見せる。 */
  let dummy_object = new THREE.Mesh(
    new THREE.CylinderBufferGeometry(bar_r, bar_r, bar_l, 1, 1),
    new THREE.MeshPhongMaterial({visible: false})); // 見せない

  let positions = [];
  for ( let i = 0; i < 4; ++i )
    positions.push(new THREE.Vector3(-bar_l/2 + i * bar_l/3, 0, 0));
  bar_curve = new THREE.CatmullRomCurve3(positions);
  bar_curve.curveType = 'catmullrom';
  bar_curve.tension = 0.4;
  bar_mesh = null;

  let shape = new Ammo.btCylinderShapeX(
    new Ammo.btVector3(bar_l/2, bar_r, bar_r));
  bar = createRigidBody(dummy_object, shape, params.bar.mass);

  // 支柱とワイヤーは物理的な実体のないただの飾り。
  pole_object = new THREE.Mesh(
    new THREE.CylinderBufferGeometry(pole_r, pole_r , bar_h+pole_r, 10, 1),
    new THREE.MeshPhongMaterial({color: params.pole.color}));
  let pole_object_ = pole_object.clone();
  pole_object.translateY(-bar_h/2).translateX(bar_l/2);
  pole_object_.translateX(-bar_l);
  pole_object.add(pole_object_);
  pole_object.visible = document.querySelector('#pole-check').checked;
  scene.add(pole_object);
  let points = [];
  for ( let pt of [
    [wire_x, -bar_h/2, wire_z],
    [0, bar_h/2, pole_r],
    [0, bar_h/2, -pole_r],
    [0 + wire_x, -bar_h/2, -wire_z],
    [0, -wire_y * bar_h + bar_h/2, pole_r],
    [0, -wire_y * bar_h + bar_h/2 , -pole_r],
    [wire_x, -bar_h/2, wire_z]
  ] ){
    points.push(new THREE.Vector3(pt[0], pt[1], pt[2]));
  }
  let wire_object = new THREE.Line(
    new THREE.BufferGeometry().setFromPoints(points),
    new THREE.LineBasicMaterial({color: params.wire.color}));
  pole_object.add(wire_object);
  for ( let point of points )
    point.x = -point.x;
  let wire_object2 = new THREE.Line(
    new THREE.BufferGeometry().setFromPoints(points),
    new THREE.LineBasicMaterial({color: params.wire.color}));
  pole_object_.add(wire_object2);

  floor = createBox(
    floor_x, floor_y, floor_z, 0, params.floor.color,
    0, -bar_h + floor_y, 0);

  body.pelvis = createEllipsoid(
    ...params.pelvis.size, params.pelvis.ratio, 0x0, 0, -1.2, 0);
  body.pelvis.setContactProcessingThreshold(-0.03);

  body.spine = createEllipsoid(
    ...params.spine.size, params.spine.ratio, 0x0,
    0, pelvis_r2 + spine_r2, 0, body.pelvis);
  // デフォルトのままだと腕に胸や腰がぶつかって背面の姿勢になれない
  body.spine.setContactProcessingThreshold(-0.03);

  body.chest = createEllipsoid(
    ...params.chest.size, params.chest.ratio, 0x0,
    0, chest_r2 + spine_r2, 0, body.spine);
  body.chest.setContactProcessingThreshold(-0.03);

  let texture = new THREE.TextureLoader().load('face.png');
  texture.offset.set(-0.25, 0);
  body.head = createEllipsoid(
    ...params.head.size, params.head.ratio, 0x0,
    0, head_r2 + chest_r2, 0, body.chest, texture);

  body.upper_leg[L] = createCylinder(
    ...params.upper_leg.size, params.upper_leg.ratio, 0x0,
    -upper_leg_x, -(pelvis_r2 + upper_leg_h/2), 0, body.pelvis);
  body.upper_leg[R] = createCylinder(
    ...params.upper_leg.size, params.upper_leg.ratio, 0x0,
    upper_leg_x, -(pelvis_r2 + upper_leg_h/2), 0, body.pelvis);

  body.lower_leg[L] = createCylinder(
    ...params.lower_leg.size, params.lower_leg.ratio, 0x0,
    -lower_leg_x, -upper_leg_h/2 - lower_leg_h/2, 0, body.upper_leg[L]);
  body.lower_leg[R] = createCylinder(
    ...params.lower_leg.size, params.lower_leg.ratio, 0x0,
    lower_leg_x, -upper_leg_h/2 - lower_leg_h/2, 0, body.upper_leg[R]);

  // 着地処理に使う見えない目印を足先に付ける。
  let mark_point = new THREE.Mesh(
    new THREE.SphereBufferGeometry(.1, 1, 1),
    new THREE.MeshPhongMaterial({colorWrite:false}));
  mark_point.position.set(0, -lower_leg_h/2, 0);
  body.lower_leg[L].three.add(mark_point);
  body.lower_leg[L].mark_point = mark_point;
  mark_point = mark_point.clone();
  body.lower_leg[R].three.add(mark_point);
  body.lower_leg[R].mark_point = mark_point;

  body.upper_arm[L] = createCylinder(
    ...params.upper_arm.size, params.upper_arm.ratio, 0x0,
    -chest_r1 - upper_arm_r, chest_r2 + upper_arm_h/2, 0, body.chest);
  body.upper_arm[R] = createCylinder(
    ...params.upper_arm.size, params.upper_arm.ratio, 0x0,
    chest_r1 + upper_arm_r, chest_r2 + upper_arm_h/2, 0, body.chest);
  if ( debug ) {
    body.upper_arm[L].three.add(new THREE.AxesHelper(3));
    body.upper_arm[R].three.add(new THREE.AxesHelper(3));
  }

  body.lower_arm[L] = createCylinder(
    ...params.lower_arm.size, params.lower_arm.ratio, 0x0,
    0, upper_arm_h/2 + lower_arm_h/2, 0, body.upper_arm[L]);
  body.lower_arm[R] = createCylinder(
    ...params.lower_arm.size, params.lower_arm.ratio, 0x0,
    0, upper_arm_h/2 + lower_arm_h/2, 0, body.upper_arm[R]);
  addHandToArm(body.lower_arm[L], lower_arm_h/2 + bar_r);
  addHandToArm(body.lower_arm[R], lower_arm_h/2 + bar_r);

  setColors();

  // 空気抵抗を受ける箇所
  gymnast.air_res_parts = [body.pelvis, body.spine, body.chest, body.head];
  gymnast.body_parts = gymnast.air_res_parts.concat(
    body.upper_leg, body.lower_leg, body.upper_arm, body.lower_arm);

  let x_axis = new Ammo.btVector3(1, 0, 0),
      y_axis = new Ammo.btVector3(0, 1, 0),
      axis;

  joint.belly = createConeTwist(
    body.pelvis, [0, pelvis_r2, 0], null,
    body.spine, [0, -spine_r2, 0], null,
    params.flexibility.belly);

  joint.breast = createConeTwist(
    body.spine, [0, spine_r2, 0], null,
    body.chest, [0, -chest_r2, 0], null,
    params.flexibility.breast);

  joint.neck = createConeTwist(
    body.chest, [0, chest_r2, 0], null,
    body.head, [0, -head_r2, 0], null,
    params.flexibility.neck);

  joint.belly.enableMotor(true);
  joint.breast.enableMotor(true);
  joint.neck.enableMotor(true);

  /* 骨盤の自由度は、膝を前に向けたまま脚を横に開く事は殆ど出来なくした。
     横に開く為には膝を横に向けないといけない。
     但し、完全に自由度を一つロックすると、不安定な動作を示す時があったので、
     一応少しだけ動くようにはした(技の動作では指定させない)。

     脚を横に開いて膝を曲げた時、足首を下に持っていく事は出来るが、
     足首を後には持っていけない。
     そういう姿勢になる鉄棒の技は多分無いので良い */
  joint.hip[L] = create6Dof(
    body.pelvis, [-upper_leg_x, -pelvis_r2, 0], [0, 0, 0],
    body.upper_leg[L], [0, upper_leg_h/2, 0], [0, 0, 0],
    [params.flexibility.hip.shift_min, params.flexibility.hip.shift_max,
     params.flexibility.hip.angle_min, params.flexibility.hip.angle_max]);
  joint.hip[R] = create6Dof(
    body.pelvis, [upper_leg_x, -pelvis_r2, 0], [0, 0, 0],
    body.upper_leg[R], [0, upper_leg_h/2, 0], [0, 0, 0],
    [params.flexibility.hip.shift_min, params.flexibility.hip.shift_max,
     params.flexibility.hip.angle_min, params.flexibility.hip.angle_max],
    'mirror');

  // HingeConstraintを繋ぐ順番によって左右不均等になってしまう。
  // どうやって修正していいか分からないが、誰でも利き腕はあるので、
  // 当面気にしない。
  joint.knee[L] = createHinge(
    body.upper_leg[L], [upper_leg_x - lower_leg_x, -upper_leg_h/2, 0], null,
    body.lower_leg[L], [0, lower_leg_h/2, 0], null,
    params.flexibility.knee);
  joint.knee[R] = createHinge(
    body.upper_leg[R], [-upper_leg_x + lower_leg_x, -upper_leg_h/2, 0], null,
    body.lower_leg[R], [0, lower_leg_h/2, 0], null,
    params.flexibility.knee);

  createShoulderJoint();

  axis = x_axis.rotate(y_axis, -120*rad_per_deg); // dataに移さず、まだ直書き
  joint.elbow[L] = createHinge(
    body.upper_arm[L], [0, upper_arm_h/2, 0], axis,
    body.lower_arm[L], [0, -lower_arm_h/2, 0], axis,
    params.flexibility.elbow);
  axis = x_axis.rotate(y_axis, 120*rad_per_deg); // dataに移さず、まだ直書き
  joint.elbow[R] = createHinge(
    body.upper_arm[R], [0, upper_arm_h/2, 0], axis,
    body.lower_arm[R], [0, -lower_arm_h/2, 0], axis,
    params.flexibility.elbow);

  joint.grip[L] = create6Dof(
    bar, [-chest_r1 - upper_arm_r, 0, 0], [Math.PI/2, 0, 0],
    body.lower_arm[L], [0, lower_arm_h/2 + bar_r, 0], null,
    [params.flexibility.grip.shift_min, params.flexibility.grip.shift_max,
     params.flexibility.grip.angle_min, params.flexibility.grip.angle_max]);
  joint.grip[L].gripping = true; // crete6Dof内でaddConstraintしてるので
  joint.grip[R] = create6Dof(
    bar, [chest_r1 + upper_arm_r, 0, 0], [Math.PI/2, 0, 0],
    body.lower_arm[R], [0, lower_arm_h/2 + bar_r, 0], null,
    [params.flexibility.grip.shift_min, params.flexibility.grip.shift_max,
     params.flexibility.grip.angle_min, params.flexibility.grip.angle_max]);
  joint.grip[R].gripping = true; // crete6Dof内でaddConstraintしてるので

  // ツイスト、逆車移行して体の向きが変った時(スイッチスタンス)のグリップ。
  // 現在は右手が軸手で、右手は握る位置は同じだが、逆手にならないように、
  // スイッチスタンスになる時に右手も握り替えて順手にする。
  joint.grip_switchst[L] = create6Dof(
    bar, [3 * (chest_r1 + upper_arm_r), 0, 0], [-Math.PI/2, Math.PI, 0],
    body.lower_arm[L], [0, lower_arm_h/2 + bar_r, 0], null,
    [params.flexibility.grip.shift_min, params.flexibility.grip.shift_max,
     params.flexibility.grip.angle_min, params.flexibility.grip.angle_max]);
  physicsWorld.removeConstraint(joint.grip_switchst[L]);
  joint.grip_switchst[L].gripping = false;
  joint.grip_switchst[R] = create6Dof(
    bar, [chest_r1 + upper_arm_r, 0, 0], [-Math.PI/2, Math.PI, 0],
    body.lower_arm[R], [0, lower_arm_h/2 + bar_r, 0], null,
    [params.flexibility.grip.shift_min, params.flexibility.grip.shift_max,
     params.flexibility.grip.angle_min, params.flexibility.grip.angle_max]);
  physicsWorld.removeConstraint(joint.grip_switchst[R]);
  joint.grip_switchst[R].gripping = false;

  motor.hip = [
    [joint.hip[L].getRotationalLimitMotor(0),
     joint.hip[L].getRotationalLimitMotor(1),
     joint.hip[L].getRotationalLimitMotor(2)],
    [joint.hip[R].getRotationalLimitMotor(0),
     joint.hip[R].getRotationalLimitMotor(1),
     joint.hip[R].getRotationalLimitMotor(2)]];

  motor.grip = [
    [joint.grip[L].getRotationalLimitMotor(0), // x軸回りは使わない
     joint.grip[L].getRotationalLimitMotor(1),
     joint.grip[L].getRotationalLimitMotor(2)],
    [joint.grip[R].getRotationalLimitMotor(0), // x軸回りは使わない
     joint.grip[R].getRotationalLimitMotor(1),
     joint.grip[R].getRotationalLimitMotor(2)]];
  motor.grip_switchst = [
    [joint.grip_switchst[L].getRotationalLimitMotor(0),
     joint.grip_switchst[L].getRotationalLimitMotor(1),
     joint.grip_switchst[L].getRotationalLimitMotor(2)],
    [joint.grip_switchst[R].getRotationalLimitMotor(0),
     joint.grip_switchst[R].getRotationalLimitMotor(1),
     joint.grip_switchst[R].getRotationalLimitMotor(2)]];

  let p = body.pelvis.three.position;
  let transform = new Ammo.btTransform();
  transform.setIdentity();
  transform.setOrigin(new Ammo.btVector3(-p.x, -p.y, -p.z));
  transform.getBasis().setEulerZYX(...[0, -Math.PI/2, 0]);
  // Generic6DofSpringConstraintに繋いだ barに繋ぐと何故かモーターが効かない
  helper_joint = new Ammo.btHingeConstraint(
    body.pelvis, transform, true);
  helper_joint.setMaxMotorImpulse(params.helper_impulse);
  helper_joint.enableMotor(true);

  transform.setIdentity();
  bar_spring =
      new Ammo.btGeneric6DofSpringConstraint(bar, transform, true);
  bar_spring.setAngularLowerLimit(new Ammo.btVector3(0, 0, 0));
  bar_spring.setAngularUpperLimit(new Ammo.btVector3(0, 0, 0));
  bar_spring.enableSpring(1, true);
  bar_spring.enableSpring(2, true);
  physicsWorld.addConstraint(bar_spring);

  /* 各関節の力を設定。
     GUIで調整できる力は、setAdjustableForces()の中で定める。
     腰の関節は、初期状態に持っていく時にいじるので、状態遷移の時に定める */
  setAdjustableForces();
}

function createEllipsoid(
  rx, ry, rz, mass_ratio, color, px, py, pz, parent, texture)
{
  let geom = new THREE.SphereBufferGeometry(1, 8, 8).scale(rx, ry, rz);
  let attr = texture ?
      {color: color, transparent: true, map: texture}: {color: color};
  let object = new THREE.Mesh(geom, new THREE.MeshPhongMaterial(attr));
  let shape = makeConvexShape(geom);
  if ( texture ) {
    object.add(new THREE.Mesh(
      geom.clone().scale(0.99, 0.99, 0.99),
      new THREE.MeshPhongMaterial({color: color})));
  }
  if ( parent ) {
    let center = parent.three.position;
    px += center.x; py += center.y; pz += center.z;
  }
  object.position.set(px, py, pz);
  return createRigidBody(object, shape, params.total_weight * mass_ratio);
}

function createCylinder(r, len, mass_ratio, color, px, py, pz, parent)
{
  let geom = new THREE.CylinderBufferGeometry(r, r, len, 10, 1);
  let object = new THREE.Mesh(
    geom, new THREE.MeshPhongMaterial({color: color}));
  let shape = new Ammo.btCylinderShape(new Ammo.btVector3(r, len/2, r));
  if ( parent ) {
    let center = parent.three.position;
    px += center.x; py += center.y; pz += center.z;
  }
  object.position.set(px, py, pz);
  return createRigidBody(object, shape, params.total_weight * mass_ratio);
}

function createBox(r1, r2, r3, mass_ratio, color, px, py, pz, parent)
{
  let geom = new THREE.BoxBufferGeometry(r1*2, r2*2, r3*2, 1, 1, 1);
  let object = new THREE.Mesh(
    geom, new THREE.MeshPhongMaterial({color: color}));
  let shape = new Ammo.btBoxShape(new Ammo.btVector3(r1, r2, r3));
  if ( parent ) {
    let center = parent.three.position;
    px += center.x; py += center.y; pz += center.z;
  }
  object.position.set(px, py, pz);
  return createRigidBody(object, shape, params.total_weight * mass_ratio);
}

function createRigidBody(object, physicsShape, mass, pos, quat, vel, angVel) {
  if ( pos ) {
    object.position.copy(pos);
  } else {
    pos = object.position;
  }

  if ( quat ) {
    object.quaternion.copy(quat);
  } else {
    quat = object.quaternion;
  }

  let transform = new Ammo.btTransform();
  transform.setIdentity();
  transform.setOrigin(new Ammo.btVector3(pos.x, pos.y, pos.z));
  transform.setRotation(new Ammo.btQuaternion(quat.x, quat.y, quat.z, quat.w));
  let motionState = new Ammo.btDefaultMotionState(transform);

  let localInertia = new Ammo.btVector3(0, 0, 0);
  physicsShape.calculateLocalInertia(mass, localInertia);

  let rbInfo = new Ammo.btRigidBodyConstructionInfo(
    mass, motionState, physicsShape, localInertia);
  let body = new Ammo.btRigidBody(rbInfo);
  body.mass = mass; // 行儀悪いけど気にしない。

  body.setFriction(0.5);

  if ( vel ) {
    body.setLinearVelocity(new Ammo.btVector3(...vel));
  }

  if ( angVel ) {
    body.setAngularVelocity(new Ammo.btVector3(...angVel));
  }

  object.userData.physicsBody = body;
  object.userData.collided = false;
  body.three = object;
  body.initial = transform;

  scene.add(object);

  if ( mass > 0 ) {
    rigidBodies.push(body);
    body.initial_transform = transform;

    // Disable deactivation
    body.setActivationState(4);
    object.initial_transform = transform;
  }

  physicsWorld.addRigidBody(body);

  return body;
}

/* limit: [liner_lower, linear_upper, angular_lower, angular_upper]
   angular_{lower/upper} limit = x, z: -180 .. 180, y: -90 .. 90

   mirror != null の時は、angular_limitに対して、左右反転する。
   (linear_limitに対しても反転しないといかんかも知れないが、
    今は使ってない(常に[0,0,0])ので気にしてない。)

   last_arg = null の時は、従来の btGeneric6DofConstraintを作り、
   それ以外の時は、last_argの Euler角順序を使った btGeneric6DofSpring2Constraint
   を作る。

   - free means upper < lower
   - locked means upper == lower
   - limited means upper > lower

   角度の回転方向が -x, -y, -z 軸方向に対しているように思われる。
   これは、btGeneric6DofConstraint, btGeneric6DofSpring2Constraint 共通。
   ↑
   この理由分った。objA, objBを繋いだモーターに対する、Aから見た回転は、
   Bを回転させるのではなく、Aを回転させると考えているのだと思う。

   btGeneric6DofSpring2Constraint では、last_argで指定する Euler角順序の
   真ん中の軸(例えば、last_arg = Ammo.RO_YZX なら Z軸)の範囲が ±90°、
   それ以外の軸の範囲が ±180°に決められている。これでは困るので、
   自力でZ軸の範囲も±180°に出来るようにした(control6DofShoulderMotors())。

   btGeneric6DofConstraintの場合は、
   モーターで指定する角度は、zyxのEuler角以外は使えない。
   つまり、最初に z軸(体の正面軸)で回し、次にy軸(捻りの軸)で回し、
   最後に x軸(宙返りの軸)で回す。但し、最初に z軸で回してしまうと、
   x軸, y軸も向きが変ってしまうので、中々思った角度に調整出来なくなる。
   姿勢によっては不可能になるが、z軸回りの回転は lockしてしまった方が
   分かり易い */
function create6Dof(
  objA, posA, eulerA = null, objB, posB, eulerB = null, limit, mirror = null,
  last_arg = null)
{
  let transform1 = new Ammo.btTransform(),
      transform2 = new Ammo.btTransform();
  if ( !eulerA ) eulerA = [0, 0, 0];
  if ( !eulerB ) eulerB = [0, 0, 0];
  transform1.setIdentity();
  transform1.getBasis().setEulerZYX(...eulerA);
  transform1.setOrigin(new Ammo.btVector3(...posA));
  transform2.setIdentity();
  transform2.getBasis().setEulerZYX(...eulerB);
  transform2.setOrigin(new Ammo.btVector3(...posB));
  let joint, constr;
  if ( last_arg !== null ) {
    constr = Ammo.btGeneric6DofSpring2Constraint;
  } else {
    constr = Ammo.btGeneric6DofConstraint;
    last_arg = true;
  }
  if ( objB !== null )
    joint = new constr(objA, objB, transform1, transform2, last_arg);
  else
    joint = new constr(objA, transform1, last_arg);
  joint.setLinearLowerLimit(new Ammo.btVector3(...limit[0]));
  joint.setLinearUpperLimit(new Ammo.btVector3(...limit[1]));
  if ( mirror != null ) {
    let tmp = [...limit[3]];
    limit[3][1] = -limit[2][1];
    limit[3][2] = -limit[2][2];
    limit[2][1] = -tmp[1];
    limit[2][2] = -tmp[2];
  }
  joint.setAngularLowerLimit(new Ammo.btVector3(...to_rads(limit[2])));
  joint.setAngularUpperLimit(new Ammo.btVector3(...to_rads(limit[3])));

  physicsWorld.addConstraint(joint, true);
  return joint;
}

function createConeTwist(
  objA, posA, eulerA = null, objB, posB, eulerB = null, limit = null)
{
  /* ConeTwistConstraint.setLimit(3,θx), setLimit(4,θy), setLimit(5,θz)

     θx, θy, θz: radianでなくdegreeで指定。

     constr.local な座標系の 原点からx軸方向、-x軸方向に向いた Cone
     (Coneの広がりは、y軸回りに±θy, z軸回りに±θz)、
     の内側にスイング動作を制限する。
     ツイストの自由度は、x軸回りに±θx (確認してないので、もしかすると
     [0..+θx]かも知れないが、きっと違う)

     setLimit(3,θx)を省くと、どうも上手く機能しない。
  */
  let transform1 = new Ammo.btTransform(),
      transform2 = new Ammo.btTransform();
  if ( !eulerA ) eulerA = [0, 0, Math.PI/2];
  if ( !eulerB ) eulerB = [0, 0, Math.PI/2];
  transform1.setIdentity();
  transform1.getBasis().setEulerZYX(...eulerA);
  transform1.setOrigin(new Ammo.btVector3(...posA));
  transform2.setIdentity();
  transform2.getBasis().setEulerZYX(...eulerB);
  transform2.setOrigin(new Ammo.btVector3(...posB));
  let joint = new Ammo.btConeTwistConstraint(
    objA, objB, transform1, transform2);
  if ( limit ) {
    limit = to_rads(limit);
    // 3: twist x-axis, 4: swing y-axis, 5: swing z-axis: constraint local
    joint.setLimit(3, limit[0]);
    joint.setLimit(4, limit[1]);
    joint.setLimit(5, limit[2]);
  }

  physicsWorld.addConstraint(joint, true);
  return joint;
}

function createHinge(
  objA, pivotA, axisA = null, objB, pivotB, axisB = null, limit = null)
{
  const x_axis = new Ammo.btVector3(1, 0, 0);
  if ( !axisA ) axisA = x_axis;
  if ( !axisB ) axisB = x_axis;
  let joint = new Ammo.btHingeConstraint(
    objA, objB,
    new Ammo.btVector3(...pivotA), new Ammo.btVector3(...pivotB),
    axisA, axisB, true);
  if ( limit )
    joint.setLimit(...to_rads([-limit[1], -limit[0]]), 0.9, 0.3, 1);

  physicsWorld.addConstraint(joint, true);
  return joint;
}

function addHandToArm(arm, y) {
  let arm_obj = arm.three;
  let geom = new THREE.SphereBufferGeometry(params.hand.size, 5, 5);
  let hand = new THREE.Mesh(
    geom, new THREE.MeshPhongMaterial({color: params.hand.color}));
  hand.position.set(0, y, 0);
  arm_obj.add(hand);
  arm_obj.hand = hand;
}

function makeConvexShape(geom) {
  let shape = new Ammo.btConvexHullShape();
  let index = geom.getIndex();
  let pts = geom.getAttribute('position');
  for ( let i = 0; i < index.count; ++i )
    shape.addPoint(new Ammo.btVector3(pts.getX(i), pts.getY(i), pts.getZ(i)));

  return shape;
}

function setHipMaxMotorForce(max, limitmax) {
  for ( let leftright = L; leftright <= R; ++leftright ) {
    for ( let xyz = 0; xyz < 3; ++xyz ) {
      let motor = gymnast.motor.hip[leftright][xyz];
      motor.m_maxMotorForce = max;
      motor.m_maxLimitForce = limitmax;
      motor.m_enableMotor = true;
    }
  }
}

/* target_angles (degree): [[left_xyz], [right_xyz]],
   dts: [[left_xyz], [right_xyz]]
   柔軟性を越えた角度指定をしても、その角度に向かう強い力を使うようになっている。
   力の指定方法は本来 dts の方を使うべきなので、良くない。 */
function controlHipMotors(target_angles, dts) {
  for ( let leftright = L; leftright <= R; ++leftright ) {
    for ( let xyz = 0; xyz < 3; ++xyz ) {
      let motor = gymnast.motor.hip[leftright][xyz],
          target_angle = target_angles[leftright][xyz] * rad_per_deg,
          dt = dts[leftright][xyz],
          angle = gymnast.joint.hip[leftright].getAngle(xyz);
      /* 毎フレーム呼び出すので、dt は変える必要があるが、
         敢えて変えないようにしてみる */
      motor.m_targetVelocity = (target_angle - angle) / dt;
    }
  }
}

function getShoulderAngle(lr) {
  /* 体操的な意味での肩角度(つまりx軸周りの角度)を返す */
  return gymnast.is_hinge_shoulder[lr]
    ? gymnast.joint.shoulder[lr].getHingeAngle()
    : -gymnast.joint.shoulder6dof[lr].getAngle(0);
}

function fixEuler(angles) {
  /* Bulletの joint.getAngle()から得られる Euler角は、腕から見た肩の回転に対応するので
     q_cur_m 0,1,2列は、腕からみたそれぞれモーターの回転x,y,z軸の成分になっている。*/
  let q_cur_m = new THREE.Matrix4().makeRotationFromEuler(
    new THREE.Euler(angles[0], angles[1], angles[2], 'YZX'));

  /* Bulletの Euler角(YZX order)では Z <= pi/2 で、z > pi/2 になろうとすると、
     x,yをpi回して z < pi/2に収める。この x,yの不連続性の為に不安定になるため、
     Blenderのオイラー角の実装
       https://developer.blender.org/diffusion/B/browse/master/source/blender/blenlib/intern/math_rotation.c
     を使って、zの範囲も -pi <= z <= pi に入れるようにする。

     Blender のオイラー角は、extrinsic order。
     又、Blenderのコードでは、回転行列が転置された定義を利用しているので、q_cur_mを転置。
     */
  q_cur_m.getInverse(q_cur_m);

  // q_cur_m_{row, col} = q_cur_m.elements[row + col*4]  (row, col = 0,1,2)
  let e = q_cur_m.elements,
      mat = [];
  for ( let row = 0; row < 3; ++row )
    mat.push([e[row], e[row + 4], e[row + 8]])

  // eul1 が Bullet の euler, eul1 と eul2で良い方を選ぶのが Blender の euler.
  let eul1 = [0,0,0], eul2 = [0,0,0];

  /* YZX order に固定。(Blender の XZY order) */
  const i = 0, j = 2, k = 1;
  let cy = Math.hypot(mat[i][i], mat[i][j]);
  if ( cy > 0.0000001 ) {
    eul1[i] = Math.atan2(mat[j][k], mat[k][k]);
	eul1[j] = Math.atan2(-mat[i][k], cy);
	eul1[k] = Math.atan2(mat[i][j], mat[i][i]);

	eul2[i] = Math.atan2(-mat[j][k], -mat[k][k]);
	eul2[j] = Math.atan2(-mat[i][k], -cy);
	eul2[k] = Math.atan2(-mat[i][j], -mat[i][i]);
  } else {
	eul1[i] = eul2[i] = Math.atan2(-mat[k][j], mat[j][j]);
	eul1[j] = eul2[j] = Math.atan2(-mat[i][k], cy);
	eul1[k] = eul2[k] = 0;
  }

  if ( Math.abs(eul1[0]) + Math.abs(eul1[1]) + Math.abs(eul1[2]) >
       Math.abs(eul2[0]) + Math.abs(eul2[1]) + Math.abs(eul2[2]) )
    eul1 = eul2;

  for ( let xyz = 0; xyz < 3; ++xyz )
    angles[xyz] = -eul1[xyz]; // parity = 1 (XZY order)
}

function affineBaseDecompose(targ_vel, joint) {
  /* 目標の角速度成分をBulletの直交しない軸に沿った角速度の成分に分ける。 */
  let xyz,
      a, axis = [],
      v = new THREE.Vector3(...targ_vel),
      mat = new THREE.Matrix3();
  for ( xyz = 0; xyz < 3; ++xyz ) {
    // xyz全部同じpointerなので axis=[0,1,2].map(i=>getAxis(i)) は使えない。
    a = joint.getAxis(xyz);
    axis.push([a.x(), a.y(), a.z()]);
  }
  mat.set(...axis[0], ...axis[1], ...axis[2])
    .transpose();
  // determinant != 0 no check. Z軸回りの角度が丁度 pi/2 の時に問題。
  mat.getInverse(mat); // THREE.js 新しい版では、 mat.invert();
  v.applyMatrix3(mat);
  [...targ_vel] = v.toArray();
}

function controlHingeShoulderMotors(leftright, targ_ang, dt) {
  /* btHingeConstraint.setMotorTarget() は、内部で getHingeAngle()
     を呼び出していて、getHingeAngle()は、角度計算に arctanを使っている。
     このせいで、素のままでは肩角度の範囲が、-pi .. pi に収まっていないと動作が
     おかしくなる。

     setMotorTarget() に相当する計算を自前で行い、
     肩の目標角度の範囲を2pi以上に出来るようにする */

  let cur_ang,
      cur_ang_extended, // shoulder_winding を考慮して範囲を広げた角度
      shoulder_impulse = gui_params['肩の力'];

  cur_ang = getShoulderAngle(leftright);

  /* アドラーのような大きな肩角度のための特別処理。
     現在は Hingeの場合しか対応してない。確認してないが6Dofでは絶対おかしくなる。 */
  if ( cur_ang - gymnast.last_shoulder_angle[leftright] < -Math.PI * 1.5 ) {
    // pi-d → pi+d' になろうとして境界を超えて -pi-d'に飛び移った
    ++gymnast.shoulder_winding[leftright];
  } else if ( cur_ang - gymnast.last_shoulder_angle[leftright] >
              Math.PI * 1.5 ) {
    // -pi+d → -pi-d' になろうとして境界を超えて pi-d'に飛び移った
    --gymnast.shoulder_winding[leftright];
  }
  gymnast.last_shoulder_angle[leftright] = cur_ang;
  cur_ang_extended =
    cur_ang + gymnast.shoulder_winding[leftright] * 2 * Math.PI;

  let target_angvel = (targ_ang - cur_ang_extended) / dt;
  gymnast.joint.shoulder[leftright].enableAngularMotor(
    true, target_angvel, shoulder_impulse);
}

function control6DofShoulderMotors(leftright, e) {
  /* 6Dofの関節の制御、かなり手こずった。腰の関節やグリップにも6Dofを使っているが、
     ここで行っている処理をやってないので、バグってるのかも知れない。

     Bulletの問題もあり色々制限がある。
     アドラーのような肩角度の指定は出来ない。
     肩を横に開く角度(z軸)は 89度までしか指定出来ない。*/

  let joint = gymnast.joint.shoulder6dof[leftright],
      joint_ang = [0, 1, 2].map(i => joint.getAngle(i)),
      targ_ang = [0, 0, 0], // 腕から見た肩のEuler角(XZY順序)
      rot_ang = [0, 0, 0],
      dt = [e[3], e[5], e[4]], // targ_angに持っていく時間。
      targ_vel;

  /* joint.getAngle() が返してくるオイラー角は、胸から見た腕の回転ではなく、
     腕から見た胸の回転。
     本当にやりたいのは、胸から見た腕の XZY intrinsic order オイラー角 で、
     これは、胸から見た YZX intrinsic order オイラー角の符号反転したものに等しい。
     そこで、6Dof jointの Euler order を YZX にしている。

     このオイラー角はZ=pi/2近辺で振動するので、オイラー角を扱い易いように修正する。*/
  fixEuler(joint_ang);

  targ_ang[0] = e[0] * rad_per_deg;
  targ_ang[2] = (leftright == L ? -1 : +1) * e[1]*rad_per_deg;
  // 腕を捻る力は、腕を絞る力が正、開く力が負。腕からみた胸の角度なので、その符号を反転。
  targ_ang[1] = (leftright == L ? +1 : -1) * e[2]*rad_per_deg;

  rot_ang = [0,1,2].map(i => targ_ang[i] - joint_ang[i]);
  targ_vel = [0,1,2].map(i => rot_ang[i] / dt[i]);

  /* 理由は全然分からないが、試しに次の2行を追加したらジンバルロックの問題も振動も
     全部解決した。

     もう一度書く。理由は全然分からない。

     但し、eul_x = eul_y = eul_z = pi/2 とかでは、まだ振動する。
     コミット 336a243ab に入れていて、今回消したコードを追加したら、
     その振動も無くせる知れないが、この振動はもう気にしないことにする。*/
  if ( Math.abs(joint_ang[2]) >= Math.PI/2 )
    targ_vel[2] = -targ_vel[2];

  /* btGeneric6DofSpring2Constraint のモーターのトルクを掛ける3軸は、
     肩のローカル座標軸でも腕のローカル座標軸でもなく、オイラー角で回転する途中の
     中途半端な斜交軸になっている。この斜交軸は、腕の回転角が大きくなると
     トルクを掛けたい軸の向きの逆方向を向き、この為に腕の振動が生まれる。

     これを無くす為に、本来掛けたいトルクを斜交軸成分に分解しなおす。
     BulletPhysicsの方を修正した方が良いと思うが、まず、こちらで試す。 */
  affineBaseDecompose(targ_vel, joint);

  for ( let xyz = 0; xyz < 3; ++xyz )
    joint.getRotationalLimitMotor(xyz).m_targetVelocity = targ_vel[xyz]

  if ( debug ) {
    for ( let xyz = 0; xyz < 3; ++xyz ) {
      if ( Math.abs(targ_vel[xyz]) < 0.01 ) {
        av[xyz].visible = false;
        continue;
      }
      av[xyz].visible = true;
      let axis = joint.getAxis(xyz),
          v = new THREE.Vector3(axis.x(), axis.y(), axis.z());
      av[xyz].setDirection(v.multiplyScalar(-Math.sign(targ_vel[xyz])));
      av[xyz].position.y = 0.5;
      av[xyz].setLength(0.15*Math.abs(targ_vel[xyz]), 0.1, 0.1);
    }
    if ( DebugLog.check() )
      console.log(`
joint_ang: ${[
  joint_ang[0]/rad_per_deg, joint_ang[1]/rad_per_deg, joint_ang[2]/rad_per_deg]}
targ: ${[
  targ_ang[0]/rad_per_deg, targ_ang[1]/rad_per_deg, targ_ang[2]/rad_per_deg]}
rot: ${[
  rot_ang[0]/rad_per_deg, rot_ang[1]/rad_per_deg, rot_ang[2]/rad_per_deg]}`);
  }
}

function controlShoulderMotors(leftright) {
  let e = curr_dousa.shoulder[leftright],
      is_hinge = e.length == 2;

  if ( is_hinge ) { // 肩角度の指定のみ。
    controlHingeShoulderMotors(leftright, -e[0] * rad_per_deg, e[1]);
  } else {
    control6DofShoulderMotors(leftright, e);
  }
}

function setGripMaxMotorForce(max, limitmax) {
  // x軸回りの回転は制御しない。但し、バーとの摩擦を導入したら使う時があるかも
  for ( let leftright = L; leftright <= R; ++leftright ) {
    for ( let yz = 1; yz < 3; ++yz ) {
      let motor = gymnast.motor.grip[leftright][yz],
          motor2 = gymnast.motor.grip_switchst[leftright][yz];
      motor.m_maxMotorForce = motor2.m_maxMotorForce = max;
      motor.m_maxLimitForce = motor2.m_maxLimitForce = limitmax;
      motor.m_enableMotor = motor2.m_enableMotor = true;
    }
  }
}

/* grip_elem[] = [left_elem, right_elem]
     left_elem, right_elem:
       'release' -- バーから手を離す。
       'catch' -- バーを掴もうとする(失敗する事もある)。
       'CATCH' -- バーを掴む(失敗しない)。リプレイ用。
       [y_angle, z_angle, dt_y, dt_z] --
            目標の角度(degree)とそこに持ってくのに掛ける時間 */
function controlGripMotors(grip_elem) {
  let elapsed = dousa_clock.getElapsedTime(),
      vects = [0,1].map(leftright => new THREE.Vector3()),
      arms = [0,1].map(leftright => gymnast.body.lower_arm[leftright].three),
      curr_joint_grip = !gymnast.is_switchst
        ? gymnast.joint.grip : gymnast.joint.grip_switchst,
      curr_grip_motors = !gymnast.is_switchst
        ? gymnast.motor.grip : gymnast.motor.grip_switchst;

  function canCatch(leftright) {
    /* ある程度、手とバーが近くないとバーをキャッチ出来ないようにする。
       キャッチする時に勢いが付き過ぎてると弾かれるようにもしたいが、
       それはやってない。

       キャッチ出来るかどうかの基準は、手とバーとの距離ではなく、
       下腕の真ん中とバーとの距離によって行う。
       これによって、手の先よりバーが遠くにあると絶対掴めないが、
       肘側にバーがあれば肘を曲げて掴む事が出来る、というのを擬似的に反映する。 */
    let dist = vects[leftright].y ** 2 + vects[leftright].z ** 2;
    return (dist < (gui_params['キャッチ幅'] * 0.01) ** 2 &&
            elapsed < gui_params['キャッチ時間']);
  }

  function resetWinding(lr) {
    gymnast.shoulder_winding[lr] = 0;
    gymnast.last_shoulder_angle[lr] = getShoulderAngle(lr);

    /* windingをリセットする時に、アドラーの後に離手した時など、
       肩角度の目標角が背面(360度ぐらい)になったままだと
       腕を一回転させようとしてしまう。
       その場凌ぎ的で嫌だが、ここで修正する */
    // 複製しないと本来の動作設定自体を上書きしてまう。嫌
    curr_dousa.shoulder =
      [[].concat(curr_dousa.shoulder[L]),
       [].concat(curr_dousa.shoulder[R])];
    if ( curr_dousa.shoulder[lr][0] > 180 )
      curr_dousa.shoulder[lr][0] -= 360;
    if ( curr_dousa.shoulder[lr][0] < -180 )
      curr_dousa.shoulder[lr][0] += 360;
  }

  function catchBar(lr, switching) {
    resetWinding(lr);
    physicsWorld.addConstraint(curr_joint_grip[lr]);
    if ( state.main == 'run' ) {
      let last_dousa = replayInfo.records[replayInfo.lastDousaPos].dousa,
          grip_copy = [].concat(last_dousa.grip);
      grip_copy[lr] = 'CATCH'; // リプレイの時に必ず成功させるようにする
      if ( switching != null )
        grip_copy.push(switching); // リプレイ時の誤差でスタンスが変わらない様に記録
      last_dousa.grip = grip_copy;
    }
    curr_joint_grip[lr].gripping = true;
  }

  function releaseBar(lr) {
    physicsWorld.removeConstraint(curr_joint_grip[lr]);
    resetWinding(lr);
    curr_joint_grip[lr].gripping = false;
  }

  function setForce(leftright) {
    if ( grip_elem[leftright] == 'catch' || grip_elem[leftright] == 'CATCH') {
      // すでに掴んでいる手を、更に掴もうとするのは意味なし
      return;
    }

    for ( let yz = 1; yz < 3; ++yz ) {
      let motor = curr_grip_motors[leftright][yz],
          target_angle = grip_elem[leftright][yz-1] * rad_per_deg,
          dt = grip_elem[leftright][yz+1],
          angle = curr_joint_grip[leftright].getAngle(yz);
      motor.m_targetVelocity = (target_angle - angle) / dt;
    }
  }

  for ( let lr = L; lr <= R; ++lr )
    arms[lr].getWorldPosition(vects[lr]);
  let switching = vects[L].x > vects[R].x; // 左手の方が右手より右に有る
  if ( grip_elem.length == 3 )
    switching = grip_elem[2]; // リプレイ時は記録されたスタンスを優先。

  if ( curr_joint_grip[L].gripping && curr_joint_grip[R].gripping ) {
    // 両手バーを掴んでいる
    for ( let leftright = L; leftright <= R; ++leftright ) {
      if ( grip_elem[leftright] == 'release' ) {
        // 離手
        releaseBar(leftright);
      } else {
        setForce(leftright);
      }
    }
  } else if ( curr_joint_grip[L].gripping && !curr_joint_grip[R].gripping ) {
    // 左手のみバーを掴んでいる
    if ( grip_elem[L] == 'release' ) {
      // 左手も離手。grip_elem[R]は無視。
      // つまり、その瞬間反対の手を掴むとかは出来ない
      releaseBar(L);
    } else if ( grip_elem[R] == 'catch' || grip_elem[R] == 'CATCH' ) {
      // 右手でバーを掴もうとする。
      // スタンスは変わらないものとする(左軸手のツイストは現在は対応してない)。
      if ( grip_elem[R] == 'CATCH' || canCatch(R) )
        catchBar(R, null);

      setForce(L);
    }
  } else if ( !curr_joint_grip[L].gripping && curr_joint_grip[R].gripping ) {
    // 右手のみバーを掴んでいる
    if ( grip_elem[R] == 'release' ) {
      // 右手も離手。grip_elem[0]は無視。
      // つまり、その瞬間反対の手を掴むとかは出来ない
      releaseBar(R);
    } else if ( grip_elem[L] == 'catch' || grip_elem[L] == 'CATCH' ) {
      // 左手でバーを掴もうとする。
      // スタンスが変わる場合(ツイスト、移行)と変わらない場合がある。
      if ( grip_elem[L] == 'CATCH' || canCatch(L) ) {
        if ( switching != gymnast.is_switchst ) {
          // スタンス変更。実際の技とは大違いだが、右手も持ち替えて順手にする
          releaseBar(L);
          releaseBar(R);
          gymnast.is_switchst = switching;
          curr_joint_grip = !gymnast.is_switchst
            ? gymnast.joint.grip : gymnast.joint.grip_switchst;
          curr_grip_motors = !gymnast.is_switchst
            ? gymnast.motor.grip : gymnast.motor.grip_switchst;
          catchBar(L, null);
          catchBar(R, switching);
        } else {
          catchBar(L, switching);
        }
      }

      setForce(R);
    }
  } else if ( !curr_joint_grip[L].gripping && !curr_joint_grip[R].gripping ) {
    // 両手離している。
    if ( switching != gymnast.is_switchst ) { // 離れ技で捻った
      gymnast.is_switchst = switching;
      curr_joint_grip = !gymnast.is_switchst
        ? gymnast.joint.grip : gymnast.joint.grip_switchst;
      curr_grip_motors = !gymnast.is_switchst
        ? gymnast.motor.grip : gymnast.motor.grip_switchst;
    }

    for ( let leftright = L; leftright <= R; ++leftright ) {
      // 離していた手を掴もうとする
      if ( grip_elem[leftright] == 'CATCH' ||
           grip_elem[leftright] == 'catch' && canCatch(leftright) )
        catchBar(leftright, switching);
    }
  }
}

function controlBody() {
  if ( state.main == 'init' )
    helper_joint.setMotorTarget(helper_joint.start_angle, 0.2);

  let q = new Ammo.btQuaternion(), e;

  for ( let leftright = L; leftright <= R; ++leftright ) {
    e = curr_dousa.knee;
    gymnast.joint.knee[leftright].setMotorTarget(
      -e[leftright][0]*rad_per_deg, e[leftright][1]);

    e = curr_dousa.elbow;
    gymnast.joint.elbow[leftright].setMotorTarget(
      -e[leftright][0]*rad_per_deg, e[leftright][1]);

    controlShoulderMotors(leftright);
  }

  e = curr_dousa.hip;
  controlHipMotors( // z軸回りのオイラー角は0で固定
    [[-e[0][0], -e[0][1], 0],
     [-e[1][0],  e[1][1], 0]],
    [[e[0][2], e[0][3], 0.2],
     [e[1][2], e[1][3], 0.2]]);

  e = curr_dousa.neck;
  q.setEulerZYX(e[0]*rad_per_deg, e[1]*rad_per_deg, e[2]*rad_per_deg);
  gymnast.joint.neck.setMotorTarget(q);

  e = curr_dousa.breast;
  q.setEulerZYX(e[0]*rad_per_deg, e[1]*rad_per_deg, e[2]*rad_per_deg);
  gymnast.joint.breast.setMotorTarget(q);

  e = curr_dousa.belly;
  q.setEulerZYX(e[0]*rad_per_deg, e[1]*rad_per_deg, e[2]*rad_per_deg);
  gymnast.joint.belly.setMotorTarget(q);

  /* x軸回りは制御しない。
     y軸正方向回り: grip側の手を軸手にして、外側に体を開く。
     z軸正方向回り: 鉄棒に対して、grip側の肩を近づけて反対側の肩を遠ざける */
  controlGripMotors(curr_dousa.grip);
}

function onWindowResize() {
  let container = document.getElementById('container');
  camera.aspect = container.offsetWidth / container.offsetHeight;
  camera.updateProjectionMatrix();
  renderer.setSize(container.offsetWidth, container.offsetHeight);
}

function animate() {
  if ( state.main == 'reset' ) {
    doResetMain();
    return;
  } else if ( state.main == 'settings' ) {
    return;
  }

  requestAnimationFrame(animate);

  let deltaTime = clock.getDelta();
  switch ( state.main ) {
  case 'run':
    renderRun(deltaTime);
    break;
  case 'replay':
    renderReplay(deltaTime);
    break;
  default:
    updatePhysics(deltaTime);
  }

  control.update();
  drawBar(); // バーをしなったように見せる

  renderer.render(scene, camera);
}

function drawBar() {
  let v = new THREE.Vector3();
  bar.three.getWorldPosition(v);
  bar_curve.points[1].y = bar_curve.points[2].y = v.y;
  bar_curve.points[1].z = bar_curve.points[2].z = v.z;
  if ( bar_mesh != null )
    scene.remove(bar_mesh);
  // 毎フレームで作り直していて無駄だが、それ以外の方法は分からなかった。
  bar_mesh = new THREE.Mesh(
    new THREE.TubeGeometry(bar_curve, 8, params.bar.size[0], 4, false),
    new THREE.MeshPhongMaterial({color: params.bar.color}));
  scene.add(bar_mesh);
}

function renderRun(deltaTime) {
  addDetailsRecord(deltaTime);
  updatePhysics(deltaTime);
}

function renderReplay(deltaTime) {
  deltaTime += replayInfo.remainingDelta;
  while ( replayInfo.replayPos < replayInfo.records.length &&
          replayInfo.records[replayInfo.replayPos].delta <= deltaTime )
  {
    let record = replayInfo.records[replayInfo.replayPos],
        p, q, vel, ang;

    deltaTime -= record.delta;

    if ( record.active_key != null ) {
      let key = (record.active_key & 0xff) == 32 ? 'space' : 'enter';
      document.querySelector('button#' + key).classList.toggle(
        'active', (record.active_key & 0x100) == 0); // 駄目実装
    }

    if ( record.dousa != null ) {
      let prev_shoulder = curr_dousa['shoulder'];
      for ( let x in record.dousa ) {
        curr_dousa[x] = record.dousa[x];
        state.entry_num = record.entry_num;
        state.waza_pos = record.waza_pos;
        showActiveWaza();
      }

      checkCurJointShoulder(prev_shoulder, curr_dousa['shoulder']);
    }

    /* キー入力の間隔が短い時に、details = null, delta = 0になる */
    if ( record.details != null ) {
      for ( let [i, elem] of Object.entries(gymnast.body_parts) ) {
        [p, q, vel, ang] = record.details[i];
        transformAux1.setIdentity();
        transformAux1.setOrigin(new Ammo.btVector3(...p));
        transformAux1.setRotation(new Ammo.btQuaternion(...q));
        elem.setWorldTransform(transformAux1);
        elem.setLinearVelocity(new Ammo.btVector3(...vel));
        elem.setAngularVelocity(new Ammo.btVector3(...ang));
      }
    }

    if ( record.delta > 0 )
      updatePhysics(record.delta);

    ++replayInfo.replayPos;
  }

  replayInfo.remainingDelta = deltaTime;
}

function updatePhysics(deltaTime) {
  DebugLog.countUp();

  let p, q;
  controlBody();
  checkLanding();
  if ( state.landing == -1 )
    applyLandingForce();
  physicsWorld.stepSimulation(
    deltaTime * gui_params['時間の流れ'], 480, 1. / params.fps);

  // Update rigid bodies
  for ( let objPhys of rigidBodies ) {
    let objThree = objPhys.three;
    let ms = objPhys.getMotionState();

    if ( ms ) {
      ms.getWorldTransform(transformAux1);
      p = transformAux1.getOrigin();
      q = transformAux1.getRotation();
      objThree.position.set(p.x(), p.y(), p.z());
      objThree.quaternion.set(q.x(), q.y(), q.z(), q.w());

      objThree.userData.collided = false;
    }
  }
}
function checkLanding() {
  /* バーを握ってる時はチェックしない。
     動作要素で、未使用の "landing" になった時しかチェックしない、という手もある。 */
  if ( gymnast.joint.grip[L].gripping || gymnast.joint.grip[R].gripping ||
       gymnast.joint.grip_switchst[L].gripping ||
       gymnast.joint.grip_switchst[R].gripping ||
       state.landing < 0 )
    return;

  /* 参考:
     https://medium.com/@bluemagnificent/collision-detection-in-javascript-3d-physics-using-ammo-js-and-three-js-31a5569291ef
     上のリンクにはコールバックを使ったやり方も書かれているが、
     現在利用している自前の ammo.js には、
     btCollisionObjectWrapperインターフェイスが、getCollisionObject()を
     公開してないため使えない(と言うか全くの空っぽ)。

     ammo.js作り直すか、最新版のに置き直すのしんどいし、コールバック使っても
     大して分り易くならないみたいだったので、下の実装でいく。

     floorと足とが少しぐらい離れてても気にしない。*/
  let dispatcher = physicsWorld.getDispatcher();
  let numManifolds = dispatcher.getNumManifolds();
  let landing = 0;
  for ( let i = 0; i < numManifolds; ++i ) {
    const manifold = dispatcher.getManifoldByIndexInternal(i),
          num_contacts = manifold.getNumContacts();
    if ( num_contacts < 1 )
      continue;

    let rb0 = Ammo.castObject(manifold.getBody0(), Ammo.btRigidBody),
        rb1 = Ammo.castObject(manifold.getBody1(), Ammo.btRigidBody);
    if ( rb0 != floor && rb1 != floor )
      continue;
    if ( rb0 == floor )
      rb0 = rb1;

    if ( gymnast.body.lower_leg.indexOf(rb0) >= 0 ) {
      landing |= (rb0 == gymnast.body.lower_leg[L]) ? 1 : 2;
    } else if ( gymnast.body.lower_arm.indexOf(rb0) < 0 ) {
      // 下腕(手は許す)、下肢以外が地面に着いたら全部着地失敗とみなす。
      landing = -2;
      break;
    }
  }

  if ( landing == 3 ) {
    state.landing = -1;
    upsideDown();
  } else {
    state.landing = landing;
  }
}

function upsideDown(enable = true) {
  // 両足が地面に着いたら、着地点に足をひっつけて、反重力を掛ける事により、
  // 下から上にぶら下げる。
  // enable == false なら、逆に、この設定を取り消して通常に戻す。
  let joint;
  if ( enable ) {
    gymnast.joint.landing = [];
    for ( let lr = L; lr <= R; ++lr ) {
      let leg = gymnast.body.lower_leg[lr];
      joint = create6Dof( // x,z軸方向の回転は制限なし
        leg, [0, -params.lower_leg.size[1]/2 - 0.03, 0], null,
        null, [0,0,0], null,
        [[-0.01,-0.01,-0.01], [0.01,0.01,0.01], [10,-10,10], [-10,10,-10]]);
      gymnast.joint.landing.push(joint);
    }

    physicsWorld.setGravity(new Ammo.btVector3(0, 9.8, 0));
  } else {
    // これ、ちゃんと jointのメモリー開放されてるか?
    while ( joint = gymnast.joint.landing.pop() )
      physicsWorld.removeConstraint(joint);
    physicsWorld.setGravity(new Ammo.btVector3(0, -9.8, 0));
  }
}

function applyLandingForce() {
  /* 着地を誤魔化す為に、着地条件が整えば水の中にいるみたいに極端に空気抵抗を増やす。 */
  const landing_air_registance = +gui_params['着地空気抵抗'],
        enable_range = +gui_params['着地補助範囲'] * rad_per_deg,
        y_axis = new THREE.Vector3(0, 1, 0);
  let p_vec, // 左右の足先の中間点
      com = getCOM(), // 重心
      lean_angle, // 重心の鉛直軸からのズレ
      sign, // 起き上がりつつある時 +, 倒れつつある時 -
      tmp = new THREE.Vector3(),
      f, vel, vel_len;
  p_vec = gymnast.body.lower_leg[L].mark_point.getWorldPosition(tmp);
  p_vec.lerp(gymnast.body.lower_leg[R].mark_point.getWorldPosition(tmp), 0.5);
  com.sub(p_vec); // 相対位置にする。
  lean_angle = Math.acos(com.dot(y_axis)/com.length());
  f = com.clone();
  f.cross(y_axis); // com, y_axis に垂直なベクトル
  f.cross(com); // com, y_axisの張る面内 comに垂直。重心に向かう方向。
  sign = Math.sign(
    gymnast.body.spine.getLinearVelocity().dot(
      new Ammo.btVector3(...f.toArray())));

  if ( lean_angle > enable_range && sign < 0 ) {
    state.landing = -2;
    upsideDown(false);
    return;
  }

  let air_resistances = [];
  for ( let body of gymnast.air_res_parts ) {
    vel = body.getLinearVelocity();
    vel_len = vel.length();

    // F = ( -v / |v| ) * (空気抵抗の係数 * |v|^2)
    f = new Ammo.btVector3(
      -vel.x() * vel_len * landing_air_registance,
      -vel.y() * vel_len * landing_air_registance,
      -vel.z() * vel_len * landing_air_registance);
    if ( f.length() > params.landing.air_max ) {
      /* f が大き過ぎると吹っ飛んでしまう */
      f.normalize();
      f.op_mul(params.landing.air_max);
    }
    air_resistances.push([f.x(), f.y(), f.z()]);
    body.applyCentralForce(f);
  }

  if ( debug ) {
    let body;
    if ( floor.arrows == null ) {
      floor.arrows = true;
      for ( body of gymnast.air_res_parts ) {
        body.air_arrow = new THREE.ArrowHelper(
          new THREE.Vector3(0,1,0), new THREE.Vector3(0,0,0));
      }
    }

    for ( body of gymnast.air_res_parts ) {
      f = new THREE.Vector3(...air_resistances.shift());
      setDebugArrow(body.air_arrow, body.three.position, f);
    }
  }
}

/* 全身の重心(THREE.Vector3)を返す。*/
function getCOM() {
  let com = [0, 0, 0],
      num = rigidBodies.length;

  for ( let body of rigidBodies ) {
    if ( body == bar )
      continue;

    let p = body.getCenterOfMassPosition();
    com[0] += p.x() / num;
    com[1] += p.y() / num;
    com[2] += p.z() / num;
  }

  return new THREE.Vector3(...com);
}

function setDebugArrow(arrow, pos, vec) {
  scene.add(arrow);

  let v = vec.clone(),
      len = v.length() / 2;
  v.normalize();
  arrow.setDirection(v);
  arrow.setLength(len);
  arrow.position.copy(pos);
}

function enableHelper(enable) {
  if ( enable ) {
    // barの位置を原点に固定しないと、helperに押されてbarが上下してしまう。
    // 開始姿勢を"静止"にすると、バーが上に押し上げられるのでよく分かる。
    bar_spring.setLinearLowerLimit(new Ammo.btVector3(0, 0, 0));
    bar_spring.setLinearUpperLimit(new Ammo.btVector3(0, 0, 0));
    physicsWorld.addConstraint(helper_joint);
  } else {
    // しなりの可動域 2m(実質制限無し)にする。
    bar_spring.setLinearLowerLimit(new Ammo.btVector3(0, -2, -2));
    bar_spring.setLinearUpperLimit(new Ammo.btVector3(0, 2, 2));
    physicsWorld.removeConstraint(helper_joint);
  }
}

function startSwing() {
  upsideDown(false);
  setCurJointShoulder(L, true);
  setCurJointShoulder(R, true);

  setHipMaxMotorForce(...params.max_force.hip_init);
  state = {
    main: 'init', entry_num: 0, waza_pos: 0, active_key: null, landing: 0 };
  let waza = start_list[composition_by_num[0]];
  let template = dousa_dict[waza_dict[waza][0][0]];
  enableHelper(true);
  helper_joint.start_angle = rad_per_deg * waza_dict[waza][0][1].angle;
  for ( let x in template )
    curr_dousa[x] = template[x];

  for ( let i = 0; i < 8; ++i ) {
    controlBody();
    physicsWorld.stepSimulation(0.2, 480, 1./240);
  }

  if ( debug && floor.arrows != null ) {
    scene.remove(gymnast.body.spine.spring_arrow);
    for ( let body of gymnast.air_res_parts )
      scene.remove(body.air_arrow);
  }

  changeButtonSettings();
  showActiveWaza();
  clock.start();
  stopRecording();
  animate();
}

function doReset() {
  // クリックした要素がフォーカスされて、
  // 以降スペースキーやエンターキーを押してもクリックしたことになってしまう
  // ので、フォーカスを外さないといけない。
  document.getElementById('reset').blur();

  // animate()の中でanimationを止めたあと、drResetMain()に飛ぶ
  state.main = 'reset';
}

function doResetMain() {
  /* start-posが変ってここに来る時には、helper_jointが付いたままになっている。
     一度外さないと、start-posが変わる度に helper_jointが一つづつ増えていく */
  enableHelper(false);

  // グリップは有ってもなくても一旦外して後から付け直す
  controlGripMotors(['release', 'release']);

  for ( let body of rigidBodies ) {
    let ms = body.getMotionState();
    ms.setWorldTransform(body.initial_transform);
    body.setMotionState(ms);
    let zero = new Ammo.btVector3(0, 0, 0);
    body.setLinearVelocity(zero);
    body.setAngularVelocity(zero);

    body.three.userData.collided = false;
  }

  gymnast.is_switchst = false;
  for ( let leftright = 0; leftright < 2; ++leftright ) {
    physicsWorld.addConstraint(gymnast.joint.grip[leftright]);
    gymnast.joint.grip[leftright].gripping = true;
  }

  gymnast.shoulder_winding[L] = gymnast.shoulder_winding[R] = 0;
  gymnast.last_shoulder_angle[L] = getShoulderAngle(L);
  gymnast.last_shoulder_angle[R] = getShoulderAngle(R);

  startSwing();
}

function changeButtonSettings() {
  switch ( state.main ) {
  case 'init':
    document.getElementById('composition').removeAttribute('disabled');
    if ( replayInfo.records.length > 3 )
      // 記録が短すぎる時は無視。以降のlengthチェックも楽になる
      document.getElementById('replay').removeAttribute('disabled');
    else
      document.getElementById('replay').setAttribute('disabled', true);
    document.querySelector('#reset').setAttribute('disabled', true);
    for ( let move of document.querySelectorAll('.move')) {
      move.removeAttribute('disabled');
      move.classList.toggle('active', false);
    }
    break;
  case 'run':
    document.getElementById('composition').setAttribute('disabled', true);
    document.getElementById('replay').setAttribute('disabled', true);
    document.querySelector('#reset').removeAttribute('disabled');
    break;
  case 'replay':
    document.getElementById('composition').setAttribute('disabled', true);
    document.getElementById('replay').setAttribute('disabled', true);
    document.querySelector('#reset').removeAttribute('disabled');
    for ( let move of document.querySelectorAll('.move'))
      move.setAttribute('disabled', true);
    break;
  default:
    // 他の状態からはこの関数は呼び出されない
    break;
  }
}

function current_waza() {
  return waza_list[composition_by_num[state.entry_num]];
}

function to_rads(degrees) {
  return degrees.map(function(d) { return d * rad_per_deg; });
}

function stopRecording() {
}

function startRecording() {
  replayInfo.records = [];
  replayInfo.lastDousaPos = 0;
  replayInfo.active_key = state.active_key;
}

function addKeyRecord(key) {
  replayInfo.records.push({
    delta: 0,
    active_key: key });
}

function addDousaRecord(dousa) {
  let copy = {};

  for ( let x in dousa )
    copy[x] = dousa[x];

  replayInfo.lastDousaPos = replayInfo.records.length;
  replayInfo.records.push({
    dousa: copy,
    entry_num: state.entry_num,
    waza_pos: state.waza_pos,
    delta: 0 });
}

function addDetailsRecord(delta) {
  let details = [],
      p, q, vel, ang;
  for ( let elem of gymnast.body_parts ) {
    elem.getMotionState().getWorldTransform(transformAux1);
    p = transformAux1.getOrigin();
    q = transformAux1.getRotation();
    vel = elem.getLinearVelocity();
    ang = elem.getAngularVelocity();
    details.push(
      [[p.x(), p.y(), p.z()],
       [q.x(), q.y(), q.z(), q.w()],
       [vel.x(), vel.y(), vel.z()],
       [ang.x(), ang.y(), ang.z()]]);
  }

  replayInfo.records.push({dousa: null, delta: delta, details: details});
}

function doReplay() {
  document.getElementById('replay').blur();
  if ( state.main != 'init' )
    return;

  state = { main: 'replay', entry_num: 1, waza_pos: 0,
            active_key: replayInfo.active_key, landing: 0 };
  changeButtonSettings();
  replayInfo.replayPos = 0;
  replayInfo.remainingDelta = 0;
  enableHelper(false);
}

Ammo().then(function(AmmoLib) {
  Ammo = AmmoLib;
  init();
  startSwing();
});
