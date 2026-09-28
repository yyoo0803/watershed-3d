(function () {
  "use strict";

  // Cesium ScreenSpaceEventType values, verified live against this VWorld build
  // (VWorld doesn't expose the Cesium namespace, so the enum can't be imported).
  var EventType = { LEFT_DOWN: 0, LEFT_UP: 1, LEFT_CLICK: 2, LEFT_DOUBLE_CLICK: 3, RIGHT_CLICK: 7, MOUSE_MOVE: 15 };
  var WATERSHED_COLORS = ["#5fd0c9", "#e8935a", "#b892e8", "#e86f9c", "#7ec8e3", "#a3d977"];
  var CATEGORY_LABEL = { general: "", before: "개발전", after: "개발후" };
  var LIFT_M = 3;
  var EARTH_RADIUS_M = 6378137;
  var TERRAIN_SPACING_OK_M = 30;
  var MAX_VERTEX_JUMP_METERS = 20000;

  function toRadians(d) { return d * Math.PI / 180; }
  function toDegrees(r) { return r * 180 / Math.PI; }

  function escapeHtml(s) {
    return String(s == null ? "" : s).replace(/[&<>"']/g, function (c) {
      return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c];
    });
  }

  var state = {
    viewer: null,
    Cartesian3: null,
    Color: null,
    EventCls: null,
    SSEH: null,
    resolution: 15,
    arrowIconUrl: null,
    watersheds: [], // {id, label, color, category, memo, visible, boundaryPositions, boundaryEntity, outlineEntity, grid, flowResults, arrowEntities, stats}
    nextWatershedNum: 1,
    editor: null,
    computeQueue: Promise.resolve(),
    tracking: { watchId: null, entity: null, hasFix: false },
    dxf: { shapes: [], anchors: [null, null], transformFn: null, previewEntities: [] }
  };

  var els = {};
  function $(id) { return document.getElementById(id); }

  function setStatus(message, level) {
    els.statusText.textContent = message;
    els.statusText.className = level || "";
  }

  function batchEntities(fn) {
    var ents = state.viewer.entities;
    ents.suspendEvents();
    try { fn(ents); } finally { ents.resumeEvents(); }
  }

  // ---------- map bootstrap ----------
  function initMap() {
    var mapOptions = new vw.MapOptions(
      vw.BasemapType.GRAPHIC,
      "",
      vw.DensityType.BASIC,
      vw.DensityType.BASIC,
      false,
      new vw.CameraPosition(
        new vw.CoordZ(127.7669, 35.9078, 900000),
        new vw.Direction(0, -90, 0)
      )
    );
    window.map = new vw.Map("vmap", mapOptions);
  }

  function waitForViewer(timeoutMs) {
    timeoutMs = timeoutMs || 10000;
    return new Promise(function (resolve, reject) {
      var start = Date.now();
      (function poll() {
        if (window.ws3d && window.ws3d.viewer && window.ws3d.viewer.scene) { resolve(window.ws3d.viewer); return; }
        if (Date.now() - start > timeoutMs) { reject(new Error("지도 초기화 시간 초과")); return; }
        setTimeout(poll, 200);
      })();
    });
  }

  function discoverTypes(viewer) {
    var globe = viewer.scene.globe;
    state.Cartesian3 = globe.ellipsoid.cartographicToCartesian({ longitude: 0, latitude: 0, height: 0 }).constructor;
    state.Color = globe.baseColor.constructor;
    state.EventCls = viewer.entities.collectionChanged.constructor;
    state.SSEH = Object.getPrototypeOf(viewer.screenSpaceEventHandler).constructor;
  }

  function cartesianToDeg(cartesian) {
    var carto = state.viewer.scene.globe.ellipsoid.cartesianToCartographic(cartesian);
    return { lng: toDegrees(carto.longitude), lat: toDegrees(carto.latitude) };
  }

  function liftCartesian(cartesian, meters) {
    var carto = state.viewer.scene.globe.ellipsoid.cartesianToCartographic(cartesian);
    return state.Cartesian3.fromRadians(carto.longitude, carto.latitude, carto.height + meters);
  }

  // A duck-typed, non-constant Cesium Property. Entities given one render through
  // Cesium's per-frame dynamic path instead of rebuilding geometry on every change,
  // which is what keeps rubber-band lines and vertex dragging smooth.
  function dynamicProperty(getter) {
    return {
      isConstant: false,
      definitionChanged: new state.EventCls(),
      getValue: function () { return getter(); },
      equals: function (other) { return other === this; }
    };
  }

  // ---------- fast terrain access ----------
  // globe.getHeight() ray-picks the rendered tile mesh (~3.4 ms per call here, which
  // froze the page for seconds on a 20x20 grid). Reading the loaded heightmap tile's
  // own interpolateHeight() gives the same value thousands of times faster.
  function rectContains(r, lon, lat) {
    return lon >= r.west && lon <= r.east && lat >= r.south && lat <= r.north;
  }
  function tileHasTerrain(t) {
    return !!(t && t.data && t.data.terrainData && typeof t.data.terrainData.interpolateHeight === "function");
  }
  function deepestTerrainTile(lon, lat) {
    var surface = state.viewer.scene.globe._surface;
    var roots = surface && surface._levelZeroTiles;
    if (!roots) return null;
    var tile = null;
    for (var i = 0; i < roots.length; i++) {
      if (tileHasTerrain(roots[i]) && rectContains(roots[i].rectangle, lon, lat)) { tile = roots[i]; break; }
    }
    while (tile) {
      var kids = [tile._southwestChild, tile._southeastChild, tile._northwestChild, tile._northeastChild];
      var next = null;
      for (var k = 0; k < 4; k++) {
        if (tileHasTerrain(kids[k]) && rectContains(kids[k].rectangle, lon, lat)) { next = kids[k]; break; }
      }
      if (!next) break;
      tile = next;
    }
    return tile;
  }
  function terrainHeightFast(lon, lat) {
    var tile = deepestTerrainTile(lon, lat);
    if (!tile) return null;
    var h = tile.data.terrainData.interpolateHeight(tile.rectangle, lon, lat);
    return (typeof h === "number" && isFinite(h)) ? h : null;
  }
  function terrainHeightDeg(lat, lng) {
    var lon = toRadians(lng), la = toRadians(lat);
    var h = terrainHeightFast(lon, la);
    if (h != null) return h;
    var g = state.viewer.scene.globe.getHeight({ longitude: lon, latitude: la });
    return (typeof g === "number" && isFinite(g)) ? g : null;
  }
  function groundHeightAt(lat, lng) {
    var h = terrainHeightDeg(lat, lng);
    return h == null ? 0 : h;
  }
  function terrainSpacingMeters(lat, lng) {
    var tile = deepestTerrainTile(toRadians(lng), toRadians(lat));
    if (!tile) return null;
    var r = tile.rectangle;
    var widthM = (r.east - r.west) * EARTH_RADIUS_M * Math.cos(toRadians(lat));
    var samples = tile.data.terrainData._width || 65;
    return widthM / Math.max(1, samples - 1);
  }
  function terrainDetailOk(points) {
    return points.every(function (p) {
      var s = terrainSpacingMeters(p.lat, p.lng);
      return s != null && s <= TERRAIN_SPACING_OK_M;
    });
  }

  // Terrain-only picking: marches the camera ray until it drops below the heightmap,
  // then bisects. Unlike scene.pickPosition it ignores our own polygons/lines, so a
  // click inside an existing (e.g. 개발전) watershed still lands on the ground.
  function pickTerrain(windowPosition) {
    var viewer = state.viewer;
    var ray = viewer.camera.getPickRay(windowPosition);
    if (!ray) return undefined;
    var ell = viewer.scene.globe.ellipsoid, C3 = state.Cartesian3;
    var o = ray.origin, d = ray.direction;
    function sample(t) {
      var c = ell.cartesianToCartographic(new C3(o.x + d.x * t, o.y + d.y * t, o.z + d.z * t));
      if (!c) return null;
      var h = terrainHeightFast(c.longitude, c.latitude);
      if (h == null) return null;
      return { diff: c.height - h, carto: c, ground: h };
    }
    var camH = viewer.camera.positionCartographic.height;
    var step = Math.max(40, camH / 25), tPrev = 0, tCur = step, limit = camH * 30 + 30000;
    var s = sample(tCur);
    while (s && s.diff > 0 && tCur < limit) { tPrev = tCur; step *= 1.25; tCur += step; s = sample(tCur); }
    if (!s || s.diff > 0) return fallbackPick(windowPosition);
    var lo = tPrev, hi = tCur, last = s;
    for (var i = 0; i < 24; i++) {
      var mid = (lo + hi) / 2, m = sample(mid);
      if (!m) break;
      last = m;
      if (m.diff > 0) lo = mid; else hi = mid;
    }
    return C3.fromRadians(last.carto.longitude, last.carto.latitude, last.ground);
  }
  function fallbackPick(windowPosition) {
    var viewer = state.viewer;
    var ray = viewer.camera.getPickRay(windowPosition);
    var c = ray ? viewer.scene.globe.pick(ray, viewer.scene) : undefined;
    return c || viewer.camera.pickEllipsoid(windowPosition, viewer.scene.globe.ellipsoid);
  }

  // Builds a terrain-hugging line: straight chords between far-apart vertices dip
  // under ridges and vanish behind the depth-tested terrain.
  function densifyPath(positions, closed, maxStepsPerSegment) {
    var n = positions.length, out = [];
    if (n === 0) return out;
    var ell = state.viewer.scene.globe.ellipsoid, C3 = state.Cartesian3;
    var maxSteps = maxStepsPerSegment || 60;
    var cartos = positions.map(function (p) { return ell.cartesianToCartographic(p); });
    var segs = closed ? n : n - 1;
    for (var i = 0; i < segs; i++) {
      var a = cartos[i], b = cartos[(i + 1) % n];
      var dist = C3.distance(positions[i], positions[(i + 1) % n]);
      var steps = Math.max(1, Math.min(maxSteps, Math.ceil(dist / 12)));
      for (var s = 0; s < steps; s++) {
        var t = s / steps;
        var lon = a.longitude + (b.longitude - a.longitude) * t;
        var lat = a.latitude + (b.latitude - a.latitude) * t;
        var h = terrainHeightFast(lon, lat);
        if (h == null) h = a.height + (b.height - a.height) * t;
        out.push(C3.fromRadians(lon, lat, h + LIFT_M));
      }
    }
    var end = closed ? cartos[0] : cartos[n - 1];
    var he = terrainHeightFast(end.longitude, end.latitude);
    out.push(C3.fromRadians(end.longitude, end.latitude, (he == null ? end.height : he) + LIFT_M));
    return out;
  }

  function midpointOnTerrain(a, b) {
    var ell = state.viewer.scene.globe.ellipsoid;
    var ca = ell.cartesianToCartographic(a), cb = ell.cartesianToCartographic(b);
    var lon = (ca.longitude + cb.longitude) / 2, lat = (ca.latitude + cb.latitude) / 2;
    var h = terrainHeightFast(lon, lat);
    if (h == null) h = (ca.height + cb.height) / 2;
    return state.Cartesian3.fromRadians(lon, lat, h);
  }

  function nextColor() {
    return WATERSHED_COLORS[(state.nextWatershedNum - 1) % WATERSHED_COLORS.length];
  }

  // ---------- camera ----------
  // VWorld re-syncs the Cesium camera from its own navigation controller every frame,
  // so viewer.camera.flyTo is silently overridden; map.moveTo is the working path.
  function flyToCoordinates(lat, lng, height) {
    var camPos = new vw.CameraPosition(new vw.CoordZ(lng, lat, height || 3000), new vw.Direction(0, -90, 0));
    window.map.moveTo(camPos);
  }

  function flyToBoundary(boundaryDeg) {
    var lngs = boundaryDeg.map(function (p) { return p.lng; });
    var lats = boundaryDeg.map(function (p) { return p.lat; });
    var minLng = Math.min.apply(null, lngs), maxLng = Math.max.apply(null, lngs);
    var minLat = Math.min.apply(null, lats), maxLat = Math.max.apply(null, lats);
    var diagonal = state.Cartesian3.distance(
      state.Cartesian3.fromDegrees(minLng, minLat, 0),
      state.Cartesian3.fromDegrees(maxLng, maxLat, 0)
    );
    flyToCoordinates((minLat + maxLat) / 2, (minLng + maxLng) / 2, Math.max(diagonal * 1.4, 400));
  }

  function geoErrorMessage(err) {
    if (err && err.code === 1) return "위치 권한이 차단되어 있습니다. 브라우저 주소창 왼쪽 자물쇠(또는 사이트 정보) 아이콘을 눌러 위치 권한을 \"허용\"으로 바꾼 뒤 새로고침하세요.";
    if (err && err.code === 2) return "위치를 확인할 수 없습니다. Windows 설정 > 개인정보 및 보안 > 위치에서 \"위치 서비스\"가 켜져 있는지, 브라우저가 허용되어 있는지 확인하세요. GPS가 없는 PC는 와이파이가 켜져 있어야 대략적인 위치를 잡습니다.";
    if (err && err.code === 3) return "위치 확인이 시간 초과되었습니다. 다시 시도해 주세요.";
    return "위치 정보를 가져올 수 없습니다. 좌표를 직접 입력하거나 주소로 검색해 주세요.";
  }

  function accuracyNote(acc) {
    var txt = "현재 위치 정확도 ±" + Math.round(acc) + "m";
    if (acc > 150) txt += "\nGPS 없이 와이파이·인터넷 주소로 추정한 위치라 오차가 큽니다. 내비게이션처럼 정확하게 쓰려면 GPS가 있는 휴대폰에서 열어야 합니다.";
    return txt;
  }

  function useMyLocation() {
    if (!navigator.geolocation) { setStatus("이 브라우저는 위치 정보를 지원하지 않습니다.", "warn"); return; }
    setStatus("현재 위치를 확인하는 중…", "");
    navigator.geolocation.getCurrentPosition(function (pos) {
      els.latInput.value = pos.coords.latitude.toFixed(6);
      els.lngInput.value = pos.coords.longitude.toFixed(6);
      flyToCoordinates(pos.coords.latitude, pos.coords.longitude, 1500);
      setStatus(accuracyNote(pos.coords.accuracy), "");
    }, function (err) {
      setStatus(geoErrorMessage(err), "warn");
    }, { enableHighAccuracy: true, timeout: 15000 });
  }

  // ---------- live location tracking (navigation-style) ----------
  function toggleTracking() {
    if (state.tracking.watchId != null) {
      navigator.geolocation.clearWatch(state.tracking.watchId);
      state.tracking.watchId = null;
      state.tracking.hasFix = false;
      if (state.tracking.entity) { state.viewer.entities.remove(state.tracking.entity); state.tracking.entity = null; }
      els.trackBtn.textContent = "실시간 위치 추적 시작";
      setStatus("실시간 위치 추적을 중지했습니다.", "");
      return;
    }
    if (!navigator.geolocation) { setStatus("이 브라우저는 위치 정보를 지원하지 않습니다.", "warn"); return; }
    els.trackBtn.textContent = "실시간 위치 추적 중지";
    setStatus("위치를 찾는 중… (처음 한 번은 브라우저가 위치 권한을 물어봅니다)", "");
    state.tracking.watchId = navigator.geolocation.watchPosition(function (pos) {
      updateTrackingMarker(pos.coords.latitude, pos.coords.longitude, pos.coords.accuracy);
    }, function (err) {
      setStatus(geoErrorMessage(err), "warn");
    }, { enableHighAccuracy: true, maximumAge: 1000, timeout: 20000 });
  }

  function updateTrackingMarker(lat, lng, accuracy) {
    var position = state.Cartesian3.fromDegrees(lng, lat, groundHeightAt(lat, lng) + LIFT_M);
    if (!state.tracking.entity) {
      state.tracking.entity = state.viewer.entities.add({
        position: position,
        point: {
          pixelSize: 15,
          color: state.Color.fromCssColorString("#2f7cf6"),
          outlineColor: state.Color.WHITE,
          outlineWidth: 3,
          disableDepthTestDistance: Number.POSITIVE_INFINITY
        }
      });
    } else {
      state.tracking.entity.position = position;
    }
    var first = !state.tracking.hasFix;
    state.tracking.hasFix = true;
    if (first || els.followCheck.checked) {
      var camH = first ? 1200 : state.viewer.camera.positionCartographic.height;
      flyToCoordinates(lat, lng, camH);
    }
    els.latInput.value = lat.toFixed(6);
    els.lngInput.value = lng.toFixed(6);
    if (!state.editor) setStatus(accuracyNote(accuracy), "");
  }

  // ---------- address / 지번 search (VWorld search API via JSONP — CORS-blocked over fetch) ----------
  var searchCallbackSeq = 0;
  function callVWorldSearch(query, category) {
    return new Promise(function (resolve, reject) {
      var cbName = "__vworldSearchCb" + (searchCallbackSeq++);
      var script = document.createElement("script");
      var timeoutId = setTimeout(function () { cleanup(); reject(new Error("timeout")); }, 8000);
      function cleanup() {
        clearTimeout(timeoutId);
        delete window[cbName];
        if (script.parentNode) script.parentNode.removeChild(script);
      }
      window[cbName] = function (data) { cleanup(); resolve(data); };
      var params = "service=search&request=search&version=2.0&crs=EPSG:4326&size=8&page=1" +
        "&query=" + encodeURIComponent(query) + "&type=address&category=" + category +
        "&format=json&errorformat=json&callback=" + cbName +
        "&key=" + encodeURIComponent((window.VWORLD_CONFIG && window.VWORLD_CONFIG.apiKey) || "");
      script.src = "https://api.vworld.kr/req/search?" + params;
      script.onerror = function () { cleanup(); reject(new Error("network")); };
      document.head.appendChild(script);
    });
  }

  function extractItems(data) {
    return (data && data.response && data.response.result && data.response.result.items) || [];
  }

  function performSearch() {
    var query = els.searchInput.value.trim();
    if (!query) return;
    setStatus("\"" + query + "\" 검색 중…", "");
    els.searchResults.hidden = true;
    callVWorldSearch(query, "parcel").then(function (data) {
      var items = extractItems(data);
      if (items.length > 0) return renderSearchResults(items);
      return callVWorldSearch(query, "road").then(function (data2) {
        var items2 = extractItems(data2);
        if (items2.length === 0) { setStatus("검색 결과가 없습니다.", "warn"); return; }
        renderSearchResults(items2);
      });
    }).catch(function () {
      setStatus("주소 검색에 실패했습니다.", "warn");
    });
  }

  function renderSearchResults(items) {
    els.searchResults.hidden = false;
    els.searchResults.innerHTML = items.map(function (item, i) {
      var addr = item.address || {};
      var label = addr.parcel || addr.road || "";
      var sub = [addr.road && addr.parcel ? addr.road : "", addr.bldnm || ""].filter(Boolean).join(" · ");
      return '<div class="search-result-item" data-i="' + i + '"><div class="sr-addr">' + escapeHtml(label) + '</div>' +
        (sub ? '<div class="sr-sub">' + escapeHtml(sub) + '</div>' : "") + '</div>';
    }).join("");
    Array.prototype.forEach.call(els.searchResults.querySelectorAll(".search-result-item"), function (el, i) {
      el.addEventListener("click", function () {
        var item = items[i];
        var lng = Number(item.point.x), lat = Number(item.point.y);
        flyToCoordinates(lat, lng, 1200);
        els.latInput.value = lat.toFixed(6);
        els.lngInput.value = lng.toFixed(6);
        els.searchResults.hidden = true;
        setStatus((item.address.parcel || item.address.road || "") + " 위치로 이동했습니다.", "");
      });
    });
  }

  // ---------- shape editor (used for drawing new boundaries and adjusting existing ones) ----------
  function startEditor(opts) {
    if (state.editor) cancelEditor();
    var ed = {
      mode: opts.mode,
      title: opts.title,
      color: opts.color,
      positions: (opts.positions || []).slice(),
      onDone: opts.onDone,
      onCancel: opts.onCancel,
      handler: null,
      outline: null,
      vertexEnts: [],
      midEnts: [],
      ringCache: [],
      hover: null,
      dragging: false,
      dragIndex: -1,
      dragMoved: false,
      suppressClick: false,
      selected: -1,
      pendingMove: null,
      moveTimer: null
    };
    state.editor = ed;
    ed.outline = state.viewer.entities.add({
      polyline: {
        positions: dynamicProperty(function () { return ed.ringCache; }),
        width: 3,
        material: state.Color.fromCssColorString(ed.color)
      }
    });
    refreshRing();
    rebuildHandles();

    ed.handler = new state.SSEH(state.viewer.scene.canvas);
    ed.handler.setInputAction(onEdLeftDown, EventType.LEFT_DOWN);
    ed.handler.setInputAction(onEdLeftUp, EventType.LEFT_UP);
    ed.handler.setInputAction(onEdLeftClick, EventType.LEFT_CLICK);
    ed.handler.setInputAction(onEdDoubleClick, EventType.LEFT_DOUBLE_CLICK);
    ed.handler.setInputAction(onEdRightClick, EventType.RIGHT_CLICK);
    ed.handler.setInputAction(onEdMouseMove, EventType.MOUSE_MOVE);
    updateEditUi();
  }

  function refreshRing() {
    var ed = state.editor;
    if (!ed) return;
    var pts = ed.positions.slice();
    if (ed.mode === "draw" && ed.hover && !ed.dragging) pts.push(ed.hover);
    ed.ringCache = pts.length >= 2 ? densifyPath(pts, pts.length >= 3) : [];
  }

  function handleStyle(ed, i) {
    var selected = i === ed.selected;
    return {
      pixelSize: selected ? 15 : 12,
      color: state.Color.fromCssColorString(selected ? "#ffe066" : "#ffffff"),
      outlineColor: state.Color.fromCssColorString(ed.color),
      outlineWidth: 3,
      disableDepthTestDistance: Number.POSITIVE_INFINITY
    };
  }

  function rebuildHandles() {
    var ed = state.editor;
    if (!ed) return;
    batchEntities(function (ents) {
      ed.vertexEnts.forEach(function (e) { ents.remove(e); });
      ed.midEnts.forEach(function (e) { ents.remove(e); });
      ed.vertexEnts = [];
      ed.midEnts = [];
      var n = ed.positions.length;
      ed.positions.forEach(function (p, i) {
        var e = ents.add({ position: liftCartesian(p, LIFT_M), point: handleStyle(ed, i) });
        e._edRole = "vertex";
        e._edIndex = i;
        ed.vertexEnts.push(e);
      });
      if (n >= 3) {
        for (var i = 0; i < n; i++) {
          var m = ents.add({
            position: liftCartesian(midpointOnTerrain(ed.positions[i], ed.positions[(i + 1) % n]), LIFT_M),
            point: {
              pixelSize: 9,
              color: state.Color.fromCssColorString(ed.color).withAlpha(0.6),
              outlineColor: state.Color.fromCssColorString("#ffffff").withAlpha(0.85),
              outlineWidth: 1,
              disableDepthTestDistance: Number.POSITIVE_INFINITY
            }
          });
          m._edRole = "mid";
          m._edIndex = i;
          ed.midEnts.push(m);
        }
      }
    });
  }

  // Cheap per-frame update while dragging: move only the dragged handle and its two
  // neighbouring midpoints instead of rebuilding every handle.
  function updateDragVisuals(i) {
    var ed = state.editor, n = ed.positions.length;
    if (ed.vertexEnts[i]) ed.vertexEnts[i].position = liftCartesian(ed.positions[i], LIFT_M);
    if (n >= 3) {
      var prev = (i - 1 + n) % n;
      if (ed.midEnts[prev]) ed.midEnts[prev].position = liftCartesian(midpointOnTerrain(ed.positions[prev], ed.positions[i]), LIFT_M);
      if (ed.midEnts[i]) ed.midEnts[i].position = liftCartesian(midpointOnTerrain(ed.positions[i], ed.positions[(i + 1) % n]), LIFT_M);
    }
  }

  function pickHandle(windowPosition) {
    var picked = state.viewer.scene.pick(windowPosition, 14, 14);
    var ent = picked && picked.id;
    if (ent && ent._edRole) return { role: ent._edRole, index: ent._edIndex };
    return null;
  }

  function setCameraLocked(locked) {
    state.viewer.scene.screenSpaceCameraController.enableInputs = !locked;
  }

  function onEdLeftDown(e) {
    var ed = state.editor;
    if (!ed) return;
    ed.suppressClick = false;
    var hit = pickHandle(e.position);
    if (!hit) return;
    ed.suppressClick = true;
    var index = hit.index;
    if (hit.role === "mid") {
      var n = ed.positions.length;
      index = hit.index + 1;
      ed.positions.splice(index, 0, midpointOnTerrain(ed.positions[hit.index], ed.positions[(hit.index + 1) % n]));
      ed.selected = index;
      rebuildHandles();
      refreshRing();
    }
    ed.dragging = true;
    ed.dragIndex = index;
    ed.dragMoved = false;
    ed.downPosition = { x: e.position.x, y: e.position.y };
    setCameraLocked(true);
  }

  function onEdLeftUp(e) {
    var ed = state.editor;
    if (!ed || !ed.dragging) return;
    // Apply the release point itself; a throttled move may still be queued.
    if (ed.moveTimer) { clearTimeout(ed.moveTimer); ed.moveTimer = null; }
    ed.pendingMove = null;
    var up = e && e.position;
    if (up && ed.downPosition && (Math.abs(up.x - ed.downPosition.x) + Math.abs(up.y - ed.downPosition.y) > 3)) {
      var c = pickTerrain(up);
      if (c) { ed.positions[ed.dragIndex] = c; ed.dragMoved = true; }
    }
    ed.dragging = false;
    setCameraLocked(false);
    if (!ed.dragMoved) ed.selected = ed.dragIndex;
    rebuildHandles();
    refreshRing();
    updateEditUi();
  }

  function onEdMouseMove(e) {
    var ed = state.editor;
    if (!ed) return;
    ed.pendingMove = { x: e.endPosition.x, y: e.endPosition.y };
    if (ed.moveTimer) return;
    ed.moveTimer = setTimeout(processPendingMove, 16);
  }

  function processPendingMove() {
    var ed = state.editor;
    if (!ed) return;
    ed.moveTimer = null;
    var p = ed.pendingMove;
    ed.pendingMove = null;
    if (!p) return;
    if (ed.dragging) {
      var c = pickTerrain(p);
      if (!c) return;
      ed.positions[ed.dragIndex] = c;
      ed.dragMoved = true;
      updateDragVisuals(ed.dragIndex);
      refreshRing();
    } else if (ed.mode === "draw" && ed.positions.length > 0) {
      ed.hover = pickTerrain(p) || null;
      refreshRing();
    }
  }

  function onEdLeftClick(e) {
    var ed = state.editor;
    if (!ed) return;
    if (ed.suppressClick) { ed.suppressClick = false; return; }
    if (ed.mode !== "draw") {
      if (ed.selected !== -1) { ed.selected = -1; rebuildHandles(); updateEditUi(); }
      return;
    }
    var c = pickTerrain(e.position);
    if (!c) return;
    var reference = ed.positions.length > 0
      ? ed.positions[ed.positions.length - 1]
      : pickTerrain({ x: Math.round(state.viewer.scene.canvas.clientWidth / 2), y: Math.round(state.viewer.scene.canvas.clientHeight / 2) });
    if (reference && state.Cartesian3.distance(reference, c) > MAX_VERTEX_JUMP_METERS) {
      setStatus("클릭 위치를 인식하지 못했습니다. 같은 지점을 다시 클릭해 주세요.", "warn");
      return;
    }
    ed.positions.push(c);
    ed.hover = null;
    rebuildHandles();
    refreshRing();
    updateEditUi();
  }

  // A double-click also fires two single clicks first, so drop the duplicate point it
  // added before finishing.
  function onEdDoubleClick() {
    var ed = state.editor;
    if (!ed || ed.mode !== "draw") return;
    var n = ed.positions.length;
    if (n >= 2 && state.Cartesian3.distance(ed.positions[n - 1], ed.positions[n - 2]) < 2) ed.positions.pop();
    editorDone();
  }

  function onEdRightClick(e) {
    var ed = state.editor;
    if (!ed) return;
    var hit = pickHandle(e.position);
    if (hit && hit.role === "vertex") deleteVertex(hit.index);
    else if (ed.mode === "draw") undoLastPoint();
  }

  function deleteVertex(i) {
    var ed = state.editor;
    if (!ed || i < 0 || i >= ed.positions.length) return;
    if (ed.mode === "edit" && ed.positions.length <= 3) {
      setStatus("유역 경계는 점이 최소 3개 있어야 합니다.", "warn");
      return;
    }
    ed.positions.splice(i, 1);
    ed.selected = -1;
    rebuildHandles();
    refreshRing();
    updateEditUi();
  }

  function undoLastPoint() {
    var ed = state.editor;
    if (!ed || ed.positions.length === 0) return;
    ed.positions.pop();
    ed.selected = -1;
    rebuildHandles();
    refreshRing();
    updateEditUi();
  }

  function teardownEditor() {
    var ed = state.editor;
    if (!ed) return;
    if (ed.handler) ed.handler.destroy();
    if (ed.moveTimer) clearTimeout(ed.moveTimer);
    batchEntities(function (ents) {
      ents.remove(ed.outline);
      ed.vertexEnts.forEach(function (e) { ents.remove(e); });
      ed.midEnts.forEach(function (e) { ents.remove(e); });
    });
    setCameraLocked(false);
    state.editor = null;
    updateEditUi();
  }

  function editorDone() {
    var ed = state.editor;
    if (!ed) return;
    if (ed.positions.length < 3) {
      setStatus("점을 3개 이상 찍어야 경계를 완성할 수 있습니다.", "warn");
      return;
    }
    var positions = ed.positions.slice();
    var cb = ed.onDone;
    teardownEditor();
    if (cb) cb(positions);
  }

  function cancelEditor() {
    var ed = state.editor;
    if (!ed) return;
    var cb = ed.onCancel;
    teardownEditor();
    if (cb) cb();
  }

  function updateEditUi() {
    var ed = state.editor;
    els.editBar.hidden = !ed;
    els.drawStartBtn.disabled = !!ed;
    els.drawFinishBtn.disabled = !ed || ed.positions.length < 3;
    if (!ed) return;
    els.editBarTitle.textContent = ed.title + " · 점 " + ed.positions.length + "개";
    els.editBarHint.textContent = ed.mode === "draw"
      ? "지도 클릭: 점 추가 · 흰 점 드래그: 이동 · 변 가운데 작은 점 드래그: 점 끼워넣기 · 흰 점 우클릭: 삭제 · 빈 곳 우클릭: 마지막 점 취소 · 더블클릭: 완료"
      : "흰 점 드래그: 이동 · 변 가운데 작은 점 드래그: 점 끼워넣기 · 흰 점 우클릭(또는 클릭 후 \"선택 점 삭제\"): 삭제 · 지도는 평소처럼 드래그로 이동";
    els.edUndoBtn.hidden = ed.mode !== "draw";
    els.edUndoBtn.disabled = ed.positions.length === 0;
    els.edDeleteBtn.disabled = ed.selected === -1;
    els.edDoneBtn.disabled = ed.positions.length < 3;
  }

  // ---------- drawing & editing entry points ----------
  function startDrawing(seedPositions, title) {
    startEditor({
      mode: "draw",
      title: title || "새 유역 그리기",
      color: nextColor(),
      positions: seedPositions || [],
      onDone: function (positions) { createWatershedFromPositions(positions, els.drawCategorySelect.value); },
      onCancel: function () { setStatus("그리기를 취소했습니다.", ""); }
    });
    setStatus(seedPositions && seedPositions.length
      ? "가져온 점 " + seedPositions.length + "개로 시작합니다. 점을 드래그해 다듬고 \"완료\"를 누르세요."
      : "지도를 클릭해 유역 경계 점을 추가하세요 (3개 이상).", "");
  }

  function beginEditWatershed(id) {
    var ws = findWatershed(id);
    if (!ws) return;
    if (state.editor) cancelEditor();
    setWatershedVisible(ws, false);
    startEditor({
      mode: "edit",
      title: ws.label + " 경계 수정",
      color: ws.color,
      positions: ws.boundaryPositions,
      onDone: function (positions) {
        if (state.watersheds.indexOf(ws) === -1) return;
        ws.boundaryPositions = positions;
        clearArrows(ws);
        buildBoundaryEntities(ws);
        setWatershedVisible(ws, true);
        ws.stats = null;
        renderWatershedList();
        computeAndRenderFlow(ws);
      },
      onCancel: function () {
        if (state.watersheds.indexOf(ws) !== -1) setWatershedVisible(ws, true);
        setStatus("수정을 취소했습니다.", "");
      }
    });
    setStatus(ws.label + " 경계를 수정합니다.", "");
  }

  function duplicateWatershed(id) {
    var ws = findWatershed(id);
    if (!ws) return;
    startDrawing(ws.boundaryPositions, ws.label + " 복제 → 새 유역");
  }

  // ---------- watersheds ----------
  function findWatershed(id) {
    return state.watersheds.filter(function (w) { return w.id === id; })[0];
  }

  function buildBoundaryEntities(ws) {
    batchEntities(function (ents) {
      if (ws.boundaryEntity) ents.remove(ws.boundaryEntity);
      if (ws.outlineEntity) ents.remove(ws.outlineEntity);
      var color = state.Color.fromCssColorString(ws.color);
      ws.boundaryEntity = ents.add({
        show: ws.visible !== false,
        polygon: {
          hierarchy: ws.boundaryPositions.map(function (p) { return liftCartesian(p, LIFT_M); }),
          material: color.withAlpha(0.14)
        }
      });
      ws.outlineEntity = ents.add({
        show: ws.visible !== false,
        polyline: { positions: densifyPath(ws.boundaryPositions, true), width: 3, material: color }
      });
    });
  }

  function setWatershedVisible(ws, visible) {
    ws.visible = visible;
    batchEntities(function () {
      if (ws.boundaryEntity) ws.boundaryEntity.show = visible;
      if (ws.outlineEntity) ws.outlineEntity.show = visible;
      ws.arrowEntities.forEach(function (e) { e.show = visible; });
    });
  }

  function createWatershedFromPositions(positions, category) {
    var ws = {
      id: "ws" + Date.now().toString(36) + Math.random().toString(36).slice(2, 6),
      label: "유역 " + state.nextWatershedNum,
      color: nextColor(),
      category: category || "general",
      memo: "",
      visible: true,
      boundaryPositions: positions,
      boundaryEntity: null,
      outlineEntity: null,
      grid: null,
      flowResults: [],
      arrowEntities: [],
      stats: null
    };
    state.nextWatershedNum += 1;
    buildBoundaryEntities(ws);
    state.watersheds.push(ws);
    els.recomputeBtn.disabled = false;
    els.resetBtn.disabled = false;
    renderWatershedList();
    computeAndRenderFlow(ws);
    return ws;
  }

  function removeWatershed(id) {
    var idx = state.watersheds.findIndex(function (w) { return w.id === id; });
    if (idx === -1) return;
    var ws = state.watersheds[idx];
    batchEntities(function (ents) {
      ws.arrowEntities.forEach(function (e) { ents.remove(e); });
      if (ws.boundaryEntity) ents.remove(ws.boundaryEntity);
      if (ws.outlineEntity) ents.remove(ws.outlineEntity);
    });
    ws.arrowEntities = [];
    state.watersheds.splice(idx, 1);
    renderWatershedList();
    if (state.watersheds.length === 0) {
      els.recomputeBtn.disabled = true;
      els.resetBtn.disabled = true;
      setStatus("지도 위에서 유역 경계를 그려보세요.", "");
    }
  }

  function resetAll() {
    if (state.editor) cancelEditor();
    state.watersheds.slice().forEach(function (ws) { removeWatershed(ws.id); });
    els.recomputeBtn.disabled = true;
    els.resetBtn.disabled = true;
    setStatus("지도 위에서 유역 경계를 그려보세요.", "");
  }

  // ---------- geometry ----------
  function isPointInPolygon(pt, ring) {
    var x = pt[0], y = pt[1];
    var inside = false;
    for (var i = 0, j = ring.length - 1; i < ring.length; j = i++) {
      var xi = ring[i][0], yi = ring[i][1];
      var xj = ring[j][0], yj = ring[j][1];
      var intersect = ((yi > y) !== (yj > y)) && (x < (xj - xi) * (y - yi) / (yj - yi) + xi);
      if (intersect) inside = !inside;
    }
    return inside;
  }

  function generateGrid(boundaryDeg, resolution) {
    var res = Math.max(3, Math.min(20, Math.round(resolution)));
    var lngs = boundaryDeg.map(function (p) { return p.lng; });
    var lats = boundaryDeg.map(function (p) { return p.lat; });
    var minLng = Math.min.apply(null, lngs), maxLng = Math.max.apply(null, lngs);
    var minLat = Math.min.apply(null, lats), maxLat = Math.max.apply(null, lats);
    var ring = boundaryDeg.map(function (p) { return [p.lng, p.lat]; });
    var grid = [];
    for (var r = 0; r < res; r++) {
      var row = [];
      var lat = minLat + (r + 0.5) * (maxLat - minLat) / res;
      for (var c = 0; c < res; c++) {
        var lng = minLng + (c + 0.5) * (maxLng - minLng) / res;
        var inside = isPointInPolygon([lng, lat], ring);
        row.push(inside ? {
          row: r, col: c, lng: lng, lat: lat, inside: true,
          height: null, cartesian: null, groundCartesian: null,
          to: null, bearing: null, slope: null, isSink: false, accumulation: 1
        } : null);
      }
      grid.push(row);
    }
    return grid;
  }

  function bearingDeg(lng1, lat1, lng2, lat2) {
    var phi1 = toRadians(lat1), phi2 = toRadians(lat2);
    var lambda1 = toRadians(lng1), lambda2 = toRadians(lng2);
    var y = Math.sin(lambda2 - lambda1) * Math.cos(phi2);
    var x = Math.cos(phi1) * Math.sin(phi2) - Math.sin(phi1) * Math.cos(phi2) * Math.cos(lambda2 - lambda1);
    return (toDegrees(Math.atan2(y, x)) + 360) % 360;
  }

  // Equirectangular approximation of polygon area — accurate enough for the
  // small (sub-km) catchments this tool draws, without needing spherical geometry.
  function boundaryAreaHectares(boundaryDeg) {
    if (boundaryDeg.length < 3) return 0;
    var lat0 = boundaryDeg.reduce(function (s, p) { return s + p.lat; }, 0) / boundaryDeg.length;
    var mPerDegLat = 110540;
    var mPerDegLng = 111320 * Math.cos(toRadians(lat0));
    var pts = boundaryDeg.map(function (p) { return [p.lng * mPerDegLng, p.lat * mPerDegLat]; });
    var area = 0;
    for (var i = 0, j = pts.length - 1; i < pts.length; j = i++) {
      area += (pts[j][0] + pts[i][0]) * (pts[j][1] - pts[i][1]);
    }
    return Math.abs(area / 2) / 10000;
  }

  function formatArea(ha) {
    return ha < 0.1 ? Math.round(ha * 10000) + "㎡" : ha.toFixed(2) + "ha";
  }

  // ---------- elevation sampling ----------
  function probePoints(boundaryDeg) {
    var pts = boundaryDeg.slice(0, 8);
    var c = boundaryDeg.reduce(function (a, p) { return { lat: a.lat + p.lat, lng: a.lng + p.lng }; }, { lat: 0, lng: 0 });
    pts.push({ lat: c.lat / boundaryDeg.length, lng: c.lng / boundaryDeg.length });
    return pts;
  }

  // The boundary was usually just drawn on screen, so detailed terrain is already
  // loaded and no camera move is needed. Only when it isn't (e.g. DXF placed
  // off-screen, or "전체 다시 계산" on a far-away watershed) fly there and wait.
  function ensureDetailedTerrain(boundaryDeg) {
    var probe = probePoints(boundaryDeg);
    if (terrainDetailOk(probe)) return Promise.resolve(false);
    flyToBoundary(boundaryDeg);
    return new Promise(function (resolve) {
      var start = Date.now();
      (function poll() {
        if (terrainDetailOk(probe) || Date.now() - start > 6000) { resolve(true); return; }
        setTimeout(poll, 300);
      })();
    });
  }

  function sampleElevations(cells, boundaryDeg) {
    return ensureDetailedTerrain(boundaryDeg).then(function () {
      cells.forEach(function (c) {
        var h = terrainHeightDeg(c.lat, c.lng);
        if (h != null) {
          c.height = h;
          c.cartesian = state.Cartesian3.fromDegrees(c.lng, c.lat, h + LIFT_M);
          c.groundCartesian = state.Cartesian3.fromDegrees(c.lng, c.lat, 0);
        }
      });
    });
  }

  // ---------- D8 flow direction + flow accumulation ----------
  var D8_DIRS = [[-1, -1], [-1, 0], [-1, 1], [0, -1], [0, 1], [1, -1], [1, 0], [1, 1]];

  function assignFlowDirections(grid) {
    var rows = grid.length, cols = grid[0].length;
    var cells = [];
    for (var r = 0; r < rows; r++) {
      for (var c = 0; c < cols; c++) {
        var cell = grid[r][c];
        if (!cell || !cell.inside || typeof cell.height !== "number") continue;
        cells.push(cell);
        var best = null, bestSlope = 0;
        for (var k = 0; k < 8; k++) {
          var nr = r + D8_DIRS[k][0], nc = c + D8_DIRS[k][1];
          if (nr < 0 || nr >= rows || nc < 0 || nc >= cols) continue;
          var n = grid[nr][nc];
          if (!n || !n.inside || typeof n.height !== "number") continue;
          var dist = state.Cartesian3.distance(cell.groundCartesian, n.groundCartesian);
          if (dist <= 0) continue;
          var slope = (cell.height - n.height) / dist;
          if (slope > bestSlope) { bestSlope = slope; best = n; }
        }
        if (best) {
          cell.to = best;
          cell.slope = bestSlope;
          cell.isSink = false;
          cell.bearing = bearingDeg(cell.lng, cell.lat, best.lng, best.lat);
        } else {
          cell.to = null;
          cell.isSink = true;
        }
      }
    }
    return cells;
  }

  // Real D8 flow accumulation: each cell starts owning 1 unit (itself), and —
  // processed from the highest cell down to the lowest, since flow direction
  // strictly decreases in elevation, so every possible upstream contributor to
  // a cell is guaranteed to be processed before it — pushes its running total
  // onto whatever cell it drains into.
  function computeFlowAccumulation(cells) {
    var ordered = cells.slice().sort(function (a, b) { return b.height - a.height; });
    ordered.forEach(function (cell) { cell.accumulation = 1; });
    ordered.forEach(function (cell) { if (cell.to) cell.to.accumulation += cell.accumulation; });
    return ordered;
  }

  function colorForCell(cell, maxAccumulation) {
    var accT = maxAccumulation > 1 ? Math.log(cell.accumulation) / Math.log(maxAccumulation) : 0;
    accT = Math.max(0, Math.min(1, accT));
    var isChannel = accT > 0.6;
    var teal = [0x5f, 0xd0, 0xc9], amber = [0xe8, 0x93, 0x5a], channelBlue = [0x4a, 0x8f, 0xe0];
    var base = isChannel ? channelBlue : teal.map(function (v, i) { return v + (amber[i] - v) * Math.max(0, Math.min(1, (cell.slope || 0) / 0.5)); });
    var hex = "#" + base.map(function (v) { return Math.round(v).toString(16).padStart(2, "0"); }).join("");
    return { hex: hex, width: isChannel ? (2 + accT * 5) : (1.5 + accT * 2), isChannel: isChannel };
  }

  function createArrowIcon() {
    var canvas = document.createElement("canvas");
    canvas.width = 32; canvas.height = 32;
    var ctx = canvas.getContext("2d");
    ctx.translate(16, 16);
    ctx.beginPath();
    ctx.moveTo(0, -12);
    ctx.lineTo(9, 10);
    ctx.lineTo(0, 4);
    ctx.lineTo(-9, 10);
    ctx.closePath();
    ctx.fillStyle = "#ffffff";
    ctx.fill();
    return canvas.toDataURL();
  }

  // ---------- rendering ----------
  function clearArrows(ws) {
    if (!ws.arrowEntities.length) return;
    batchEntities(function (ents) { ws.arrowEntities.forEach(function (e) { ents.remove(e); }); });
    ws.arrowEntities = [];
  }

  function renderFlowArrows(ws) {
    clearArrows(ws);
    var cells = ws.flowResults;
    var maxAcc = cells.reduce(function (m, c) { return Math.max(m, c.accumulation); }, 1);
    var show = ws.visible !== false;
    batchEntities(function (ents) {
      cells.forEach(function (cell) {
        if (cell.isSink) {
          ws.arrowEntities.push(ents.add({
            show: show,
            position: cell.cartesian,
            point: {
              pixelSize: 8,
              color: state.Color.fromCssColorString("#ff6b6b"),
              outlineColor: state.Color.WHITE,
              outlineWidth: 1,
              disableDepthTestDistance: Number.POSITIVE_INFINITY
            }
          }));
          return;
        }
        var mid = state.Cartesian3.lerp(cell.cartesian, cell.to.cartesian, 0.55, new state.Cartesian3(0, 0, 0));
        var color = colorForCell(cell, maxAcc);
        var material = state.Color.fromCssColorString(color.hex);
        ws.arrowEntities.push(ents.add({
          show: show,
          polyline: { positions: [cell.cartesian, mid], width: color.width, material: material }
        }));
        // rotation = toRadians(-bearing) verified live: an east-bearing arrow points east.
        ws.arrowEntities.push(ents.add({
          show: show,
          position: mid,
          billboard: {
            image: state.arrowIconUrl,
            rotation: toRadians(-cell.bearing),
            color: material,
            scale: color.isChannel ? 0.9 : 0.6,
            disableDepthTestDistance: Number.POSITIVE_INFINITY
          }
        }));
      });
    });
  }

  // ---------- orchestration ----------
  // Computations run one at a time, so "전체 다시 계산" no longer launches several
  // camera flights and grid samplings on top of each other.
  function computeAndRenderFlow(ws) {
    state.computeQueue = state.computeQueue
      .then(function () { return computeFlowNow(ws); })
      .catch(function () {
        setStatus(ws.label + ": 계산 중 문제가 발생했습니다. 다시 시도해 주세요.", "error");
      });
    return state.computeQueue;
  }

  function computeFlowNow(ws) {
    if (state.watersheds.indexOf(ws) === -1 || ws.boundaryPositions.length < 3) return Promise.resolve();
    setStatus("지형 표고를 조회하는 중… (" + ws.label + ")", "");
    var boundaryDeg = ws.boundaryPositions.map(cartesianToDeg);
    var grid = generateGrid(boundaryDeg, state.resolution);
    var flatCells = [];
    grid.forEach(function (row) { row.forEach(function (cell) { if (cell) flatCells.push(cell); }); });
    if (flatCells.length === 0) {
      setStatus(ws.label + ": 경계 내부에 격자점이 생성되지 않았습니다. 경계를 더 크게 그려보세요.", "warn");
      return Promise.resolve();
    }
    return sampleElevations(flatCells, boundaryDeg).then(function () {
      if (state.watersheds.indexOf(ws) === -1) return;
      var validCells = flatCells.filter(function (c) { return typeof c.height === "number"; });
      if (validCells.length === 0) {
        setStatus(ws.label + ": 지형 표고 조회에 실패했습니다. 다른 위치로 이동하거나 해상도를 낮춰 다시 시도하세요.", "error");
        return;
      }
      ws.grid = grid;
      ws.flowResults = computeFlowAccumulation(assignFlowDirections(grid));
      renderFlowArrows(ws);
      var sinkCount = ws.flowResults.filter(function (f) { return f.isSink; }).length;
      var maxAcc = ws.flowResults.reduce(function (m, c) { return Math.max(m, c.accumulation); }, 1);
      var areaHa = boundaryAreaHectares(boundaryDeg);
      ws.stats = {
        pointCount: flatCells.length,
        failedCount: flatCells.length - validCells.length,
        sinkCount: sinkCount,
        maxAccumulation: maxAcc,
        areaHa: areaHa
      };
      renderWatershedList();
      if (!state.editor) {
        setStatus(
          ws.label + " · 격자점 " + flatCells.length + "개(실패 " + ws.stats.failedCount + ") · " +
          "면적 약 " + formatArea(areaHa) + " · 싱크 " + sinkCount + "개 · 최대 흐름누적 " + maxAcc + "\n" +
          "굵은 파란 선 = 흐름누적이 높은 추정 하도, 나머지는 경사에 따라 옅은청록~주황.\n" +
          "D8 방향+흐름누적 기반 간이 추정이며, 실제 유역분석 소프트웨어를 대체하지 않습니다.",
          ""
        );
      }
    });
  }

  function recomputeAll() {
    state.watersheds.forEach(function (ws) { computeAndRenderFlow(ws); });
  }

  // ---------- watershed list UI ----------
  function renderWatershedList() {
    els.watershedCount.textContent = state.watersheds.length;
    var has = state.watersheds.length > 0;
    els.exportCsvBtn.disabled = !has;
    els.exportGeoJsonBtn.disabled = !has;
    if (!has) {
      els.watershedList.innerHTML = '<div class="ws-empty">아직 그린 유역이 없습니다.</div>';
      return;
    }
    var focusedId = document.activeElement && document.activeElement.classList.contains("ws-memo")
      ? document.activeElement.getAttribute("data-id") : null;
    els.watershedList.innerHTML = state.watersheds.map(function (ws) {
      var meta = ws.stats
        ? (ws.stats.pointCount + "점 · " + formatArea(ws.stats.areaHa) + " · 싱크" + ws.stats.sinkCount + " · 누적max" + ws.stats.maxAccumulation)
        : "계산 중…";
      var tag = ws.category && ws.category !== "general" ? '<span class="ws-tag ' + ws.category + '">' + CATEGORY_LABEL[ws.category] + '</span>' : "";
      return (
        '<div class="ws-row ws-card" data-id="' + ws.id + '">' +
          '<div class="ws-head">' +
            '<span class="ws-dot" style="background:' + ws.color + '"></span>' +
            '<button class="ws-name" data-act="fly" title="이 유역으로 이동">' + escapeHtml(ws.label) + '</button>' + tag +
            '<button class="ws-btn" data-act="edit" title="경계 점을 드래그해 조정">수정</button>' +
            '<button class="ws-btn" data-act="copy" title="이 경계를 복사해 새 유역으로 다듬기">복제</button>' +
            '<button class="ws-del" data-act="del" aria-label="' + escapeHtml(ws.label) + ' 삭제">×</button>' +
          '</div>' +
          '<div class="ws-meta">' + meta + '</div>' +
          '<textarea class="ws-memo" data-id="' + ws.id + '" placeholder="메모…">' + escapeHtml(ws.memo || "") + '</textarea>' +
        '</div>'
      );
    }).join("");
    if (focusedId) {
      var ta = els.watershedList.querySelector('.ws-memo[data-id="' + focusedId + '"]');
      if (ta) { ta.focus(); ta.setSelectionRange(ta.value.length, ta.value.length); }
    }
  }

  function onWatershedListClick(e) {
    var btn = e.target.closest("[data-act]");
    if (!btn) return;
    var row = btn.closest(".ws-card");
    var id = row && row.getAttribute("data-id");
    var ws = findWatershed(id);
    if (!ws) return;
    var act = btn.getAttribute("data-act");
    if (act === "fly") flyToBoundary(ws.boundaryPositions.map(cartesianToDeg));
    else if (act === "edit") beginEditWatershed(id);
    else if (act === "copy") duplicateWatershed(id);
    else if (act === "del") {
      if (state.editor && state.editor.title.indexOf(ws.label) === 0) cancelEditor();
      removeWatershed(id);
    }
  }

  function onWatershedListInput(e) {
    if (!e.target.classList.contains("ws-memo")) return;
    var ws = findWatershed(e.target.getAttribute("data-id"));
    if (ws) ws.memo = e.target.value;
  }

  // ---------- DXF import ----------
  function findDxfShape(id) {
    return state.dxf.shapes.filter(function (s) { return s.id === id; })[0];
  }

  function extractShapesFromDxf(dxf) {
    var shapes = [];
    (dxf.entities || []).forEach(function (e, idx) {
      if ((e.type === "LWPOLYLINE" || e.type === "POLYLINE") && Array.isArray(e.vertices) && e.vertices.length >= 2) {
        shapes.push({ id: "s" + idx, kind: e.shape ? "polygon" : "line", layer: e.layer || "", vertices: e.vertices.map(function (v) { return { x: v.x, y: v.y }; }) });
      } else if (e.type === "LINE" && Array.isArray(e.vertices) && e.vertices.length === 2) {
        shapes.push({ id: "s" + idx, kind: "line", layer: e.layer || "", vertices: e.vertices.map(function (v) { return { x: v.x, y: v.y }; }) });
      } else if (e.type === "HATCH" && Array.isArray(e.boundaryPaths)) {
        e.boundaryPaths.forEach(function (bp, bi) {
          var verts = [];
          if (Array.isArray(bp.vertices)) {
            verts = bp.vertices.map(function (v) { return { x: v.x, y: v.y }; });
          } else if (Array.isArray(bp.edges)) {
            bp.edges.forEach(function (edge) {
              if (edge.start) verts.push({ x: edge.start.x, y: edge.start.y });
              if (edge.end) verts.push({ x: edge.end.x, y: edge.end.y });
              if (edge.center && typeof edge.radius === "number") {
                var a0 = edge.startAngle || 0, a1 = edge.endAngle != null ? edge.endAngle : 360;
                var step = Math.max(5, (a1 - a0) / 8);
                for (var a = a0; a <= a1; a += step) {
                  var rad = a * Math.PI / 180;
                  verts.push({ x: edge.center.x + edge.radius * Math.cos(rad), y: edge.center.y + edge.radius * Math.sin(rad) });
                }
              }
            });
          }
          if (verts.length >= 3) shapes.push({ id: "s" + idx + "_" + bi, kind: "polygon", layer: e.layer || "", vertices: verts, isHatch: true });
        });
      }
    });
    return shapes;
  }

  function prefillDxfAnchors(shapes) {
    var minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
    shapes.forEach(function (s) {
      s.vertices.forEach(function (v) {
        if (v.x < minX) minX = v.x; if (v.x > maxX) maxX = v.x;
        if (v.y < minY) minY = v.y; if (v.y > maxY) maxY = v.y;
      });
    });
    if (!isFinite(minX)) return;
    els.dxfAnchor1X.value = minX; els.dxfAnchor1Y.value = minY;
    els.dxfAnchor2X.value = maxX; els.dxfAnchor2Y.value = maxY;
  }

  function handleDxfFile(file) {
    if (!file) return;
    if (typeof DxfParser === "undefined") {
      els.dxfStatus.textContent = "DXF 파서를 불러오지 못했습니다. 인터넷 연결을 확인해 주세요.";
      return;
    }
    var reader = new FileReader();
    reader.onload = function () {
      var dxf;
      try {
        dxf = new DxfParser().parseSync(reader.result);
      } catch (e) {
        els.dxfStatus.textContent = "DXF 파싱 실패: " + e.message;
        return;
      }
      var shapes = extractShapesFromDxf(dxf);
      if (shapes.length === 0) {
        els.dxfStatus.textContent = "인식 가능한 도형(선·폴리라인·해치)을 찾지 못했습니다.";
        return;
      }
      clearDxfPreview();
      state.dxf.shapes = shapes;
      state.dxf.anchors = [null, null];
      state.dxf.transformFn = null;
      els.dxfAnchor1Status.textContent = "";
      els.dxfAnchor2Status.textContent = "";
      els.dxfStatus.textContent = shapes.length + "개 도형을 찾았습니다. 기준점 2개를 지도에서 지정하세요.";
      prefillDxfAnchors(shapes);
      els.dxfAnchorPanel.hidden = false;
      renderDxfShapeList();
    };
    reader.readAsText(file);
  }

  function armAnchorPick(index) {
    if (state.editor) { setStatus("먼저 그리기/수정을 완료하거나 취소한 뒤 기준점을 지정하세요.", "warn"); return; }
    setStatus("지도를 클릭해 기준점 " + (index + 1) + "의 실제 위치를 지정하세요.", "");
    var handler = new state.SSEH(state.viewer.scene.canvas);
    handler.setInputAction(function (click) {
      var cartesian = pickTerrain(click.position);
      handler.destroy();
      if (!cartesian) { setStatus("클릭 위치를 인식하지 못했습니다. 다시 시도하세요.", "warn"); return; }
      var deg = cartesianToDeg(cartesian);
      var xInput = index === 0 ? els.dxfAnchor1X : els.dxfAnchor2X;
      var yInput = index === 0 ? els.dxfAnchor1Y : els.dxfAnchor2Y;
      state.dxf.anchors[index] = { lat: deg.lat, lng: deg.lng, dxfX: Number(xInput.value), dxfY: Number(yInput.value) };
      (index === 0 ? els.dxfAnchor1Status : els.dxfAnchor2Status).textContent = "지정됨 ✓";
      setStatus("기준점 " + (index + 1) + " 지정 완료.", "");
      maybeApplyDxfTransform();
    }, EventType.LEFT_CLICK);
  }

  function maybeApplyDxfTransform() {
    var a1 = state.dxf.anchors[0], a2 = state.dxf.anchors[1];
    if (!a1 || !a2) return;
    var mPerDegLat = 110540, mPerDegLng = 111320 * Math.cos(toRadians(a1.lat));
    var m2 = { x: (a2.lng - a1.lng) * mPerDegLng, y: (a2.lat - a1.lat) * mPerDegLat };
    var dP = { x: a2.dxfX - a1.dxfX, y: a2.dxfY - a1.dxfY };
    var distP = Math.sqrt(dP.x * dP.x + dP.y * dP.y);
    var distM = Math.sqrt(m2.x * m2.x + m2.y * m2.y);
    if (distP === 0 || distM === 0) { setStatus("기준점 두 개의 DXF 좌표 또는 지도 위치가 같습니다. 서로 다른 지점을 선택하세요.", "warn"); return; }
    var scale = distM / distP;
    var theta = Math.atan2(m2.y, m2.x) - Math.atan2(dP.y, dP.x);
    var cosT = Math.cos(theta), sinT = Math.sin(theta);
    state.dxf.transformFn = function (p) {
      var rx = p.x - a1.dxfX, ry = p.y - a1.dxfY;
      var rotX = rx * cosT - ry * sinT, rotY = rx * sinT + ry * cosT;
      return { lng: a1.lng + rotX * scale / mPerDegLng, lat: a1.lat + rotY * scale / mPerDegLat };
    };
    renderDxfPreview();
    setStatus("DXF 도형이 지도에 배치되었습니다. 목록에서 유역으로 가져오거나 이어그릴 수 있습니다.", "");
  }

  function clearDxfPreview() {
    if (!state.dxf.previewEntities.length) return;
    batchEntities(function (ents) { state.dxf.previewEntities.forEach(function (e) { ents.remove(e); }); });
    state.dxf.previewEntities = [];
  }

  function renderDxfPreview() {
    clearDxfPreview();
    var fn = state.dxf.transformFn;
    if (!fn) return;
    var totalVerts = state.dxf.shapes.reduce(function (s, sh) { return s + sh.vertices.length; }, 0);
    var maxSteps = totalVerts > 3000 ? 1 : 20;
    batchEntities(function (ents) {
      state.dxf.shapes.forEach(function (shape) {
        shape.cartesians = shape.vertices.map(fn).map(function (p) {
          return state.Cartesian3.fromDegrees(p.lng, p.lat, groundHeightAt(p.lat, p.lng));
        });
        var closed = shape.kind === "polygon";
        if (closed) {
          state.dxf.previewEntities.push(ents.add({
            polygon: {
              hierarchy: shape.cartesians.map(function (c) { return liftCartesian(c, LIFT_M); }),
              material: state.Color.fromCssColorString(shape.isHatch ? "#ffe08a" : "#ffffff").withAlpha(shape.isHatch ? 0.28 : 0.1)
            }
          }));
        }
        state.dxf.previewEntities.push(ents.add({
          polyline: { positions: densifyPath(shape.cartesians, closed, maxSteps), width: 2, material: state.Color.fromCssColorString("#ffffff") }
        }));
      });
    });
  }

  function renderDxfShapeList() {
    els.dxfShapeCount.textContent = state.dxf.shapes.length;
    els.dxfShapeList.innerHTML = state.dxf.shapes.map(function (shape, i) {
      var kindLabel = shape.kind === "polygon" ? (shape.isHatch ? "해치" : "폐합 도형") : "선";
      return (
        '<div class="ws-row">' +
          '<div class="ws-info"><div class="ws-label">도형 ' + (i + 1) + '</div>' +
          '<div class="ws-meta">' + kindLabel + ' · ' + shape.vertices.length + '점 · 레이어 ' + escapeHtml(shape.layer) + '</div></div>' +
          '<button class="btn btn-sm" data-dxf="import" data-id="' + shape.id + '">유역으로</button>' +
          '<button class="btn btn-sm" data-dxf="draw" data-id="' + shape.id + '">다듬기</button>' +
        '</div>'
      );
    }).join("");
  }

  function onDxfListClick(e) {
    var btn = e.target.closest("[data-dxf]");
    if (!btn) return;
    var shape = findDxfShape(btn.getAttribute("data-id"));
    if (!shape || !shape.cartesians || shape.cartesians.length < 3) {
      setStatus("먼저 기준점 2개를 지정해 도형을 지도에 배치하세요.", "warn");
      return;
    }
    if (btn.getAttribute("data-dxf") === "import") createWatershedFromPositions(shape.cartesians.slice(), els.drawCategorySelect.value);
    else startDrawing(shape.cartesians.slice(), "DXF 도형 다듬기 → 새 유역");
  }

  // ---------- export ----------
  function downloadFile(content, filename, mime) {
    var blob = new Blob([content], { type: mime });
    var url = URL.createObjectURL(blob);
    var a = document.createElement("a");
    a.href = url; a.download = filename;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    setTimeout(function () { URL.revokeObjectURL(url); }, 1000);
  }

  function exportCsv() {
    var rows = ["watershed,category,memo,lng,lat,elevation_m,flow_to_lng,flow_to_lat,bearing_deg,slope,accumulation,is_sink"];
    state.watersheds.forEach(function (ws) {
      var memo = '"' + (ws.memo || "").replace(/"/g, '""') + '"';
      ws.flowResults.forEach(function (c) {
        rows.push([
          ws.label, ws.category || "general", memo,
          c.lng.toFixed(6), c.lat.toFixed(6), c.height.toFixed(2),
          c.isSink ? "" : c.to.lng.toFixed(6), c.isSink ? "" : c.to.lat.toFixed(6),
          c.isSink ? "" : c.bearing.toFixed(1), c.isSink ? "" : c.slope.toFixed(4),
          c.accumulation, c.isSink ? 1 : 0
        ].join(","));
      });
    });
    downloadFile("﻿" + rows.join("\n"), "watershed_flow.csv", "text/csv");
  }

  function exportGeoJson() {
    var features = [];
    state.watersheds.forEach(function (ws) {
      var ring = ws.boundaryPositions.map(cartesianToDeg).map(function (p) { return [p.lng, p.lat]; });
      if (ring.length) ring.push(ring[0]);
      features.push({
        type: "Feature",
        properties: { type: "boundary", watershed: ws.label, category: ws.category || "general", memo: ws.memo || "", color: ws.color, area_ha: ws.stats ? ws.stats.areaHa : null },
        geometry: { type: "Polygon", coordinates: [ring] }
      });
      ws.flowResults.forEach(function (c) {
        features.push({
          type: "Feature",
          properties: {
            type: "cell", watershed: ws.label, elevation_m: c.height,
            bearing_deg: c.isSink ? null : c.bearing, slope: c.isSink ? null : c.slope,
            accumulation: c.accumulation, is_sink: c.isSink
          },
          geometry: { type: "Point", coordinates: [c.lng, c.lat] }
        });
        if (!c.isSink) {
          features.push({
            type: "Feature",
            properties: { type: "flow", watershed: ws.label, slope: c.slope, accumulation: c.accumulation },
            geometry: { type: "LineString", coordinates: [[c.lng, c.lat], [c.to.lng, c.to.lat]] }
          });
        }
      });
    });
    downloadFile(JSON.stringify({ type: "FeatureCollection", features: features }, null, 1), "watershed_flow.geojson", "application/geo+json");
  }

  // ---------- UI wiring ----------
  function onKeyDown(e) {
    if (!state.editor) return;
    var tag = (e.target && e.target.tagName) || "";
    if (tag === "INPUT" || tag === "TEXTAREA" || tag === "SELECT") return;
    if (e.key === "Enter") { e.preventDefault(); editorDone(); }
    else if (e.key === "Escape") { e.preventDefault(); cancelEditor(); }
    else if (e.key === "Backspace" || e.key === "Delete") {
      e.preventDefault();
      if (state.editor.selected !== -1) deleteVertex(state.editor.selected);
      else if (state.editor.mode === "draw") undoLastPoint();
    } else if ((e.key === "z" || e.key === "Z") && (e.ctrlKey || e.metaKey) && state.editor.mode === "draw") {
      e.preventDefault();
      undoLastPoint();
    }
  }

  function setupUI() {
    els.flyBtn.addEventListener("click", function () {
      var lat = Number(els.latInput.value), lng = Number(els.lngInput.value);
      if (!isFinite(lat) || !isFinite(lng) || (lat === 0 && lng === 0)) { setStatus("위도/경도를 올바르게 입력해 주세요.", "warn"); return; }
      flyToCoordinates(lat, lng);
    });
    els.myLocationBtn.addEventListener("click", useMyLocation);
    els.trackBtn.addEventListener("click", toggleTracking);
    els.searchBtn.addEventListener("click", performSearch);
    els.searchInput.addEventListener("keydown", function (e) { if (e.key === "Enter") performSearch(); });

    els.dxfUploadBtn.addEventListener("click", function () { els.dxfInput.click(); });
    els.dxfInput.addEventListener("change", function () { handleDxfFile(els.dxfInput.files[0]); els.dxfInput.value = ""; });
    els.dxfPick1Btn.addEventListener("click", function () { armAnchorPick(0); });
    els.dxfPick2Btn.addEventListener("click", function () { armAnchorPick(1); });
    els.dxfShapeList.addEventListener("click", onDxfListClick);

    els.resolutionSlider.addEventListener("input", function () {
      state.resolution = Number(els.resolutionSlider.value);
      els.resolutionLabel.textContent = state.resolution;
      els.resolutionLabel2.textContent = state.resolution;
    });
    els.drawStartBtn.addEventListener("click", function () { startDrawing(); });
    els.drawFinishBtn.addEventListener("click", editorDone);
    els.recomputeBtn.addEventListener("click", recomputeAll);
    els.resetBtn.addEventListener("click", resetAll);
    els.exportCsvBtn.addEventListener("click", exportCsv);
    els.exportGeoJsonBtn.addEventListener("click", exportGeoJson);
    els.watershedList.addEventListener("click", onWatershedListClick);
    els.watershedList.addEventListener("input", onWatershedListInput);

    els.edUndoBtn.addEventListener("click", undoLastPoint);
    els.edDeleteBtn.addEventListener("click", function () { if (state.editor) deleteVertex(state.editor.selected); });
    els.edCancelBtn.addEventListener("click", cancelEditor);
    els.edDoneBtn.addEventListener("click", editorDone);
    document.addEventListener("keydown", onKeyDown);

    els.panelToggle.addEventListener("click", function () { els.controls.classList.toggle("open"); });
    els.retryBtn.addEventListener("click", function () { window.location.reload(); });
    renderWatershedList();
    renderDxfShapeList();
    updateEditUi();
  }

  function showLoadError(err) {
    els.loadErrorMsg.textContent = (err && err.message ? err.message + " — " : "") +
      "config.js의 apiKey/domain 설정을 확인한 뒤 다시 시도해 주세요.";
    els.loadError.hidden = false;
  }

  function cacheEls() {
    [
      "controls", "statusText", "latInput", "lngInput", "flyBtn", "myLocationBtn", "trackBtn", "followCheck",
      "searchInput", "searchBtn", "searchResults",
      "dxfInput", "dxfUploadBtn", "dxfStatus", "dxfAnchorPanel", "dxfAnchor1X", "dxfAnchor1Y", "dxfAnchor2X", "dxfAnchor2Y",
      "dxfPick1Btn", "dxfPick2Btn", "dxfAnchor1Status", "dxfAnchor2Status", "dxfShapeCount", "dxfShapeList",
      "resolutionSlider", "resolutionLabel", "resolutionLabel2", "drawCategorySelect",
      "drawStartBtn", "drawFinishBtn", "recomputeBtn", "resetBtn",
      "watershedCount", "watershedList", "exportCsvBtn", "exportGeoJsonBtn",
      "editBar", "editBarTitle", "editBarHint", "edUndoBtn", "edDeleteBtn", "edCancelBtn", "edDoneBtn",
      "panelToggle", "loadError", "loadErrorMsg", "retryBtn"
    ].forEach(function (id) { els[id] = $(id); });
  }

  function initApp() {
    cacheEls();
    setStatus("지도를 초기화하는 중…", "");
    if (typeof vw === "undefined") {
      showLoadError(new Error("VWorld 스크립트를 불러오지 못했습니다."));
      return;
    }
    try {
      initMap();
    } catch (e) {
      showLoadError(e);
      return;
    }
    waitForViewer()
      .then(function (viewer) {
        state.viewer = viewer;
        discoverTypes(viewer);
        viewer.scene.globe.depthTestAgainstTerrain = true;
        state.arrowIconUrl = createArrowIcon();
        setupUI();
        setStatus("지도가 준비되었습니다. 주소를 검색하거나 좌표로 이동한 뒤, 유역 경계를 그려보세요.", "");
      })
      .catch(function (err) {
        showLoadError(err);
      });
  }

  window.addEventListener("DOMContentLoaded", initApp);
})();
