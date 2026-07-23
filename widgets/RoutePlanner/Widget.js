// RoutePlanner widget — network-graph route calculator over the app's
// live Routes (polyline) and Waypoints (point) hosted feature layers.
//
// Rendering runs on the widget's own embedded Leaflet map (vendored locally
// under libs/leaflet/, not the app's shared ArcGIS Map) for speed and a
// simpler lng/lat-native rendering path — no spatial-reference projection
// needed. Data access (query + edit) still goes through the ArcGIS JS API
// against the hosted feature services directly by URL.
//
// Written in ES5 throughout (var, function expressions, string
// concatenation) to match this app's stated IE11 support requirement.
define([
  'dojo/_base/declare',
  'dojo/_base/lang',
  'dojo/_base/array',
  'dojo/on',
  'dojo/dom-construct',
  'dojo/dom-class',
  'dojo/Deferred',
  'jimu/BaseWidget',
  'dojo/text!./Widget.html',
  'esri/tasks/query',
  'esri/tasks/QueryTask',
  'esri/layers/FeatureLayer',
  'esri/graphic',
  'esri/geometry/Point',
  'esri/SpatialReference'
], function (
  declare, lang, array, on, domConstruct, domClass, Deferred,
  BaseWidget, template,
  EsriQuery, QueryTask, FeatureLayer,
  Graphic, EsriPoint, SpatialReference
) {

  // ======================================================================
  // MODULE-LEVEL GEO HELPERS (no turf.js dependency — plain haversine +
  // planar segment projection, same approximation turf itself uses at
  // this regional scale).
  // ======================================================================
  var EARTH_RADIUS_KM = 6371.0088;

  function toRad(deg) { return deg * Math.PI / 180; }

  function haversineKm(lng1, lat1, lng2, lat2) {
    var dLat = toRad(lat2 - lat1);
    var dLng = toRad(lng2 - lng1);
    var a = Math.sin(dLat / 2) * Math.sin(dLat / 2) +
      Math.cos(toRad(lat1)) * Math.cos(toRad(lat2)) *
      Math.sin(dLng / 2) * Math.sin(dLng / 2);
    var c = 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1 - a));
    return EARTH_RADIUS_KM * c;
  }

  // Closest point on segment [a,b] to point p, in plain lng/lat space —
  // used only to pick which point along a segment is nearest; the actual
  // reported distance is always re-measured with haversineKm afterwards.
  function projectPointOnSegment(a, b, p) {
    var abx = b[0] - a[0], aby = b[1] - a[1];
    var apx = p[0] - a[0], apy = p[1] - a[1];
    var lenSq = abx * abx + aby * aby;
    var t = lenSq === 0 ? 0 : (apx * abx + apy * aby) / lenSq;
    if (t < 0) t = 0;
    if (t > 1) t = 1;
    return { point: [a[0] + abx * t, a[1] + aby * t], t: t };
  }

  // Nearest point on a polyline (array of [lng,lat] coords) to point p.
  // Returns { coordinates:[lng,lat], location: km-from-line-start, distKm }.
  function nearestPointOnLineCoords(coords, p) {
    var best = null;
    var travelled = 0;
    for (var i = 0; i < coords.length - 1; i++) {
      var a = coords[i], b = coords[i + 1];
      var segLenKm = haversineKm(a[0], a[1], b[0], b[1]);
      var proj = projectPointOnSegment(a, b, p);
      var distKm = haversineKm(p[0], p[1], proj.point[0], proj.point[1]);
      var locationKm = travelled + segLenKm * proj.t;
      if (!best || distKm < best.distKm) {
        best = { coordinates: proj.point, distKm: distKm, location: locationKm };
      }
      travelled += segLenKm;
    }
    return best;
  }

  function formatDuration(hours) {
    if (!isFinite(hours) || hours < 0) return '-';
    var totalMinutes = Math.round(hours * 60);
    var h = Math.floor(totalMinutes / 60);
    var m = totalMinutes % 60;
    return h === 0 ? (m + 'm') : (h + 'h ' + m + 'm');
  }

  function formatCoords(lat, lng) {
    if (typeof lat !== 'number' || typeof lng !== 'number') return '-';
    return lat.toFixed(5) + ', ' + lng.toFixed(5);
  }

  function escapeHtml(s) {
    return String(s == null ? '' : s)
      .replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
  }

  // Binary min-heap keyed on distance — Dijkstra frontier.
  function MinHeap() { this.items = []; }
  MinHeap.prototype.size = function () { return this.items.length; };
  MinHeap.prototype.push = function (dist, key) {
    this.items.push([dist, key]);
    var i = this.items.length - 1;
    while (i > 0) {
      var parent = (i - 1) >> 1;
      if (this.items[parent][0] <= this.items[i][0]) break;
      var tmp = this.items[parent]; this.items[parent] = this.items[i]; this.items[i] = tmp;
      i = parent;
    }
  };
  MinHeap.prototype.pop = function () {
    var top = this.items[0];
    var last = this.items.pop();
    if (this.items.length > 0) {
      this.items[0] = last;
      var i = 0, n = this.items.length;
      while (true) {
        var smallest = i, left = 2 * i + 1, right = 2 * i + 2;
        if (left < n && this.items[left][0] < this.items[smallest][0]) smallest = left;
        if (right < n && this.items[right][0] < this.items[smallest][0]) smallest = right;
        if (smallest === i) break;
        var tmp = this.items[smallest]; this.items[smallest] = this.items[i]; this.items[i] = tmp;
        i = smallest;
      }
    }
    return top;
  };

  function edgeId(a, b) { return a < b ? (a + '|' + b) : (b + '|' + a); }

  // ======================================================================
  // WIDGET
  // ======================================================================
  return declare([BaseWidget], {

    templateString: template,
    baseClass: 'jimu-widget-routeplanner',

    postCreate: function () {
      this.inherited(arguments);
      this._injectCss();

      this.waypoints = [];
      this.networkGraph = { nodes: {}, adj: {} };
      this.nodeGrid = null;
      this.nodeGridMaxRadius = 0;
      this._routeCoordSegments = [];
      this.selectedDepWp = null;
      this.selectedArrWp = null;
      this.lastCalculatedRoute = null;
      this._routesReady = false;
      this._waypointsReady = false;
      this._waypointsLayerUrl = null;
      this._waypointsEditLayer = null;
      this._isAddingWaypoint = false;
      this._pendingWaypointMarker = null;
      this._toastTimer = null;

      this.own(on(this.calcBtn, 'click', lang.hitch(this, this.onCalculateClick)));
      this.own(on(this.resetBtn, 'click', lang.hitch(this, this.onResetClick)));
      this.own(on(this.exportBtn, 'click', lang.hitch(this, this.onExportCsvClick)));
      this.own(on(this.toleranceInput, 'change', lang.hitch(this, this._validateTolerance)));
      this.own(on(document.body, 'click', lang.hitch(this, this._onDocumentClick)));

      this.toleranceInput.value = this.config.defaultToleranceMeters || 300;
      this.speedInput.value = this.config.defaultAvgSpeedKmh || 40;

      // Data loading (ArcGIS QueryTask, independent of the app's ArcGIS Map)
      // and Leaflet asset loading run in parallel — nothing here waits on
      // the app's shared Map component being ready.
      this._loadNetworkData();
      this._loadLeafletAssets().then(lang.hitch(this, function () {
        this._initLeafletMap();
      }), function (err) {
        console.error('RoutePlanner: failed to load Leaflet', err);
      });
    },

    onOpen: function () {
      this.inherited(arguments);
      if (this.leafletMap) {
        var self = this;
        setTimeout(function () { self.leafletMap.invalidateSize(); }, 0);
      }
    },

    destroy: function () {
      if (this.leafletMap) { this.leafletMap.remove(); this.leafletMap = null; }
      this.inherited(arguments);
    },

    _injectCss: function (href) {
      href = href || (this.folderUrl + 'css/style.css');
      var existing = document.querySelectorAll('link[href="' + href + '"]');
      if (existing.length === 0) {
        domConstruct.create('link', { rel: 'stylesheet', href: href }, document.head);
      }
    },

    _showLoading: function (msg) {
      this.loadingTextNode.innerHTML = escapeHtml(msg || 'Working…');
      domClass.add(this.loadingOverlayNode, 'rp-active');
    },
    _hideLoading: function () {
      domClass.remove(this.loadingOverlayNode, 'rp-active');
    },

    _showToast: function (msg, isError) {
      if (this._toastTimer) { clearTimeout(this._toastTimer); this._toastTimer = null; }
      this.toastNode.innerHTML = escapeHtml(msg);
      this.toastNode.className = 'rp-toast ' + (isError ? 'rp-toast-error' : 'rp-toast-ok');
      this.toastNode.style.display = 'block';
      var self = this;
      this._toastTimer = setTimeout(function () { self.toastNode.style.display = 'none'; }, 4000);
    },

    // ====================================================================
    // LEAFLET MAP (widget's own embedded map — independent of the app's
    // shared ArcGIS Map, vendored locally so it works without CDN access).
    // ====================================================================
    _loadLeafletAssets: function () {
      var deferred = new Deferred();
      if (window.L) { deferred.resolve(window.L); return deferred.promise; }

      this._injectCss(this.folderUrl + 'libs/leaflet/leaflet.css');

      var existingScript = document.querySelector('script[data-rp-leaflet]');
      if (existingScript) {
        on.once(existingScript, 'load', function () { deferred.resolve(window.L); });
        on.once(existingScript, 'error', function (err) { deferred.reject(err); });
        return deferred.promise;
      }

      var script = document.createElement('script');
      script.setAttribute('data-rp-leaflet', '1');
      script.src = this.folderUrl + 'libs/leaflet/leaflet.js';
      script.onload = function () { deferred.resolve(window.L); };
      script.onerror = function (err) { deferred.reject(err); };
      document.head.appendChild(script);

      return deferred.promise;
    },

    _initLeafletMap: function () {
      var L = window.L;
      this.leafletMap = L.map(this.mapNode, {
        center: [35.0, 38.2],
        zoom: 7,
        preferCanvas: true
      });

      L.tileLayer(this.config.basemapTileUrlTemplate, {
        attribution: this.config.basemapAttribution || '',
        maxZoom: this.config.basemapMaxZoom || 19
      }).addTo(this.leafletMap);

      this.baseWaypointsLayerGroup = L.layerGroup().addTo(this.leafletMap);
      this.routeLayerGroup = L.layerGroup().addTo(this.leafletMap);

      // Leaflet's map object isn't a DOM node, and dojo/on's duck-typed
      // delegation to a target's own .on/.off is unverified for it here —
      // bind directly with Leaflet's native event API instead. No manual
      // unbind needed: leafletMap.remove() in destroy() tears down all of
      // the map's own listeners internally.
      this.leafletMap.on('click', lang.hitch(this, this._onMapClick));

      if (this.waypoints.length > 0) this._renderBaseWaypointsLayer();
    },

    _leafletIcon: function (kind, opts) {
      var L = window.L;
      opts = opts || {};
      if (kind === 'num') {
        return L.divIcon({
          className: 'rp-map-icon',
          html: '<div class="rp-pin-num" style="background:' + opts.color + '">' + opts.label + '</div>',
          iconSize: [20, 20], iconAnchor: [10, 10]
        });
      }
      if (kind === 'kiss') {
        return L.divIcon({
          className: 'rp-map-icon',
          html: '<div class="rp-pin-kiss">&#8644;</div>',
          iconSize: [26, 26], iconAnchor: [13, 13]
        });
      }
      if (kind === 'endpoint') {
        return L.divIcon({
          className: 'rp-map-icon',
          html: '<div class="rp-pin-endpoint" style="background:' + opts.color + '"><span>' + opts.label + '</span></div>',
          iconSize: [24, 24], iconAnchor: [12, 22]
        });
      }
      if (kind === 'new') {
        return L.divIcon({ className: 'rp-map-icon', html: '<div class="rp-pin-new"></div>', iconSize: [18, 18], iconAnchor: [9, 9] });
      }
      return L.divIcon({ className: 'rp-map-icon', html: '<div class="rp-pin-num" style="background:#94a3b8">?</div>', iconSize: [20, 20], iconAnchor: [10, 10] });
    },

    _renderBaseWaypointsLayer: function () {
      if (!this.leafletMap) return;
      var L = window.L;
      this.baseWaypointsLayerGroup.clearLayers();
      array.forEach(this.waypoints, function (wp) {
        if (wp.lng == null || wp.lat == null) return;
        L.circleMarker([wp.lat, wp.lng], {
          radius: 4, color: '#64748b', weight: 1, fillColor: '#94a3b8', fillOpacity: 0.75
        }).bindTooltip(escapeHtml(wp.name), { direction: 'top' }).addTo(this.baseWaypointsLayerGroup);
      }, this);

      if (!this.lastCalculatedRoute) {
        var pts = array.filter(this.waypoints, function (w) { return w.lat != null && w.lng != null; })
          .map(function (w) { return [w.lat, w.lng]; });
        if (pts.length > 0) {
          var bounds = L.latLngBounds(pts);
          if (bounds.isValid()) this.leafletMap.fitBounds(bounds, { padding: [30, 30], maxZoom: 10 });
        }
      }
    },

    _setBaseWaypointsDimmed: function (dimmed) {
      if (!this.baseWaypointsLayerGroup) return;
      this.baseWaypointsLayerGroup.eachLayer(function (l) {
        l.setStyle({ opacity: dimmed ? 0.25 : 1, fillOpacity: dimmed ? 0.2 : 0.75 });
      });
    },

    // ====================================================================
    // DATA LOADING — resolve Routes/Waypoints layers by configured URL
    // (falling back to a title match in the app's ArcGIS Map, if present),
    // query every feature (paged), build the routing graph.
    // ====================================================================
    _findOperationalLayerDefByTitle: function (opLayers, title) {
      var lowerTitle = String(title || '').toLowerCase();
      var found = null;
      array.forEach(opLayers || [], lang.hitch(this, function (def) {
        if (found) return;
        if (def.title && String(def.title).toLowerCase() === lowerTitle) { found = def; return; }
        if (def.layers && def.layers.length) {
          var nested = this._findOperationalLayerDefByTitle(def.layers, title);
          if (nested) found = nested;
        }
      }));
      return found;
    },

    _collectLayerTitles: function (opLayers, out) {
      out = out || [];
      array.forEach(opLayers || [], lang.hitch(this, function (def) {
        if (def.title) out.push(def.title);
        if (def.layers && def.layers.length) this._collectLayerTitles(def.layers, out);
      }));
      return out;
    },

    // Configured *LayerUrl wins when present — these are known hosted-service
    // URLs and querying them directly works whether or not the layer is
    // actually added as an operational layer in the webmap (e.g. a
    // routing-only "dissolved" network layer that's never drawn on the map).
    // Title-matching against the webmap's operational layers is only a
    // fallback for when no URL is configured.
    _resolveLayerUrl: function (titleConfigKey, urlConfigKey, label) {
      var configuredUrl = urlConfigKey && this.config[urlConfigKey];
      if (configuredUrl) {
        return { url: configuredUrl, source: 'configured URL' };
      }

      var opLayers = (this.map && this.map.itemInfo && this.map.itemInfo.itemData &&
        this.map.itemInfo.itemData.operationalLayers) || [];
      var title = this.config[titleConfigKey];
      var def = this._findOperationalLayerDefByTitle(opLayers, title);

      if (def && def.url) {
        return { url: def.url, source: 'map layer "' + def.title + '"' };
      }

      var titles = this._collectLayerTitles(opLayers, []);
      throw new Error(
        label + ' layer "' + title + '" not found in the map (case-insensitive title match), ' +
        'and no "' + urlConfigKey + '" is configured. Layers in this map: ' +
        (titles.length ? titles.join(', ') : '(none)') +
        '. Fix widgets/RoutePlanner/config.json.'
      );
    },

    // Queries every feature from a layer URL, paging with start/num, always
    // requesting WGS84 (4326) output so all downstream math is plain
    // lng/lat degrees regardless of the service's native spatial reference.
    _queryAllFeatures: function (url) {
      var deferred = new Deferred();
      var queryTask = new QueryTask(url);
      var pageSize = 1000;
      var allFeatures = [];
      var maxPages = 200; // safety cap
      var prevFirstStamp = null;

      // Identity stamp for a page's first feature — if a service ignores
      // start/num (no pagination support), every "page" comes back
      // identical; this catches that instead of looping to maxPages while
      // silently appending the same 1000 features over and over.
      function stampOf(feat) {
        if (!feat) return null;
        return JSON.stringify(feat.attributes) + '|' + (feat.geometry ? feat.geometry.x + ',' + feat.geometry.y : '');
      }

      function fetchPage(start, pageIndex) {
        var q = new EsriQuery();
        q.where = '1=1';
        q.outFields = ['*'];
        q.returnGeometry = true;
        q.outSpatialReference = new SpatialReference({ wkid: 4326 });
        q.start = start;
        q.num = pageSize;

        queryTask.execute(q, function (result) {
          var feats = result.features || [];
          var firstStamp = stampOf(feats[0]);
          if (pageIndex > 0 && firstStamp !== null && firstStamp === prevFirstStamp) {
            console.warn('RoutePlanner: layer at ' + url + ' does not appear to support paging (start/num ignored) — stopping after ' + allFeatures.length + ' features.');
            deferred.resolve(allFeatures);
            return;
          }
          prevFirstStamp = firstStamp;
          allFeatures = allFeatures.concat(feats);
          if (feats.length === pageSize && pageIndex < maxPages) {
            fetchPage(start + pageSize, pageIndex + 1);
          } else {
            deferred.resolve(allFeatures);
          }
        }, function (err) {
          deferred.reject(err);
        });
      }

      fetchPage(0, 0);
      return deferred.promise;
    },

    _loadNetworkData: function () {
      this._loadRoutes();
      this._loadWaypoints();
    },

    _loadRoutes: function () {
      this.routesStatusNode.innerHTML = 'Loading Routes layer…';
      domClass.remove(this.routesStatusNode, 'rp-status-ok rp-status-error');
      try {
        var layerInfo = this._resolveLayerUrl('routesLayerTitle', 'routesLayerUrl', 'Routes');
      } catch (err) {
        this._onRoutesError(err);
        return;
      }
      this._queryAllFeatures(layerInfo.url).then(lang.hitch(this, function (features) {
        try {
          this._buildGraphFromRouteFeatures(features);
          this._routesReady = true;
          this.routesStatusNode.innerHTML =
            'Loaded ' + features.length + ' route segments (' + layerInfo.source + ')';
          domClass.add(this.routesStatusNode, 'rp-status-ok');
          this._checkReadyToCalculate();
        } catch (err) {
          this._onRoutesError(err);
        }
      }), lang.hitch(this, this._onRoutesError));
    },

    _onRoutesError: function (err) {
      console.error('RoutePlanner: routes load failed', err);
      this.routesStatusNode.innerHTML = 'Failed to load Routes layer: ' + escapeHtml(err && err.message || err);
      domClass.add(this.routesStatusNode, 'rp-status-error');
    },

    _loadWaypoints: function () {
      this.waypointsStatusNode.innerHTML = 'Loading Waypoints layer…';
      domClass.remove(this.waypointsStatusNode, 'rp-status-ok rp-status-error');
      try {
        var layerInfo = this._resolveLayerUrl('waypointsLayerTitle', 'waypointsLayerUrl', 'Waypoints');
      } catch (err) {
        this._onWaypointsError(err);
        return;
      }
      this._waypointsLayerUrl = layerInfo.url;
      this._queryAllFeatures(layerInfo.url).then(lang.hitch(this, function (features) {
        try {
          var fields = this.config.waypointFields || {};
          var idField = fields.idField || 'fid';
          var nameField = fields.nameField || 'name';
          var typeField = fields.typeField || 'type';
          var kissField = fields.kissPointField || 'kisspoint';
          var kissTrueValues = array.map(this.config.kissPointTrueValues || ['yes', 'true', '1'], function (v) {
            return String(v).toLowerCase();
          });

          this.waypoints = array.map(features, function (f) {
            var attrs = f.attributes || {};
            var kissRaw = String(attrs[kissField] == null ? '' : attrs[kissField]).toLowerCase();
            return {
              id: attrs[idField],
              name: attrs[nameField] || ('Waypoint ' + attrs[idField]),
              type: attrs[typeField] || '',
              isKissPoint: array.indexOf(kissTrueValues, kissRaw) !== -1,
              lng: f.geometry ? f.geometry.x : null,
              lat: f.geometry ? f.geometry.y : null
            };
          });

          this._waypointsReady = true;
          this.waypointsStatusNode.innerHTML =
            'Loaded ' + this.waypoints.length + ' waypoints (' + layerInfo.source + ')';
          domClass.add(this.waypointsStatusNode, 'rp-status-ok');

          this.depInput.disabled = false;
          this.arrInput.disabled = false;
          this.addWaypointBtn.disabled = false;
          this.depInput.placeholder = 'Search departure...';
          this.arrInput.placeholder = 'Search arrival...';

          if (this.leafletMap) this._renderBaseWaypointsLayer();

          this._checkReadyToCalculate();
        } catch (err) {
          this._onWaypointsError(err);
        }
      }), lang.hitch(this, this._onWaypointsError));
    },

    _onWaypointsError: function (err) {
      console.error('RoutePlanner: waypoints load failed', err);
      this.waypointsStatusNode.innerHTML = 'Failed to load Waypoints layer: ' + escapeHtml(err && err.message || err);
      domClass.add(this.waypointsStatusNode, 'rp-status-error');
    },

    // ====================================================================
    // GRAPH ENGINE
    // ====================================================================
    _pickRoadName: function (attrs) {
      var candidates = this.config.routeNameFields || ['Road', 'road', 'NAME', 'Name', 'name'];
      for (var i = 0; i < candidates.length; i++) {
        if (attrs[candidates[i]]) return attrs[candidates[i]];
      }
      return 'Corridor';
    },

    _buildGraphFromRouteFeatures: function (features) {
      var nodes = {}, adj = {};
      var segments = [];

      function getNodeKey(coord) { return coord[0].toFixed(6) + ',' + coord[1].toFixed(6); }
      function addNode(key, coord) {
        if (!nodes[key]) { nodes[key] = coord; adj[key] = []; }
      }
      function addEdge(k1, k2, dist, roadName, coordsSegment) {
        adj[k1].push({ to: k2, dist: dist, road: roadName, coords: coordsSegment });
        adj[k2].push({ to: k1, dist: dist, road: roadName, coords: [coordsSegment[1], coordsSegment[0]] });
      }

      array.forEach(features, lang.hitch(this, function (feature) {
        var paths = feature.geometry && feature.geometry.paths;
        if (!paths) return;
        var roadName = this._pickRoadName(feature.attributes || {});
        array.forEach(paths, function (coords) {
          for (var i = 0; i < coords.length - 1; i++) {
            var p1 = coords[i], p2 = coords[i + 1];
            var k1 = getNodeKey(p1), k2 = getNodeKey(p2);
            addNode(k1, p1);
            addNode(k2, p2);
            var segDist = haversineKm(p1[0], p1[1], p2[0], p2[1]);
            addEdge(k1, k2, segDist, roadName, [p1, p2]);
            segments.push([p1, p2]);
          }
        });
      }));

      this.networkGraph = { nodes: nodes, adj: adj };
      this._routeCoordSegments = segments;

      this._mergeNearbyGraphNodes();
      this._buildNodeGrid();
    },

    // Bridges dead-end (degree-1) vertices to their nearest neighbor within
    // SNAP_TOLERANCE_KM — corrects hand-digitized junction gaps without a
    // blanket merge that could weld unrelated roads together.
    _mergeNearbyGraphNodes: function () {
      var SNAP_TOLERANCE_KM = 0.1; // 100m
      var nodes = this.networkGraph.nodes, adj = this.networkGraph.adj;
      var keys = [];
      for (var k in nodes) { if (nodes.hasOwnProperty(k)) keys.push(k); }
      if (keys.length === 0) return;

      var degree1Keys = array.filter(keys, function (k) { return (adj[k] || []).length === 1; });
      if (degree1Keys.length === 0) return;

      var cellDeg = 0.01; // ~1.1km, well above SNAP_TOLERANCE_KM
      var grid = {};
      array.forEach(keys, function (key) {
        var lng = nodes[key][0], lat = nodes[key][1];
        var cellKey = Math.floor(lng / cellDeg) + ',' + Math.floor(lat / cellDeg);
        if (!grid[cellKey]) grid[cellKey] = [];
        grid[cellKey].push(key);
      });

      var parent = {};
      array.forEach(keys, function (k) { parent[k] = k; });
      function find(x) {
        while (parent[x] !== x) { parent[x] = parent[parent[x]]; x = parent[x]; }
        return x;
      }
      function union(a, b) {
        var ra = find(a), rb = find(b);
        if (ra !== rb) parent[ra] = rb;
      }

      array.forEach(degree1Keys, function (key) {
        var lng = nodes[key][0], lat = nodes[key][1];
        var cx = Math.floor(lng / cellDeg), cy = Math.floor(lat / cellDeg);
        var bestKey = null, bestDist = Infinity;
        for (var dx = -1; dx <= 1; dx++) {
          for (var dy = -1; dy <= 1; dy++) {
            var bucket = grid[(cx + dx) + ',' + (cy + dy)];
            if (!bucket) continue;
            array.forEach(bucket, function (otherKey) {
              if (otherKey === key) return;
              var d = haversineKm(lng, lat, nodes[otherKey][0], nodes[otherKey][1]);
              if (d < bestDist) { bestDist = d; bestKey = otherKey; }
            });
          }
        }
        if (bestKey && bestDist <= SNAP_TOLERANCE_KM) union(key, bestKey);
      });

      var mergedNodes = {}, mergedAdj = {};
      array.forEach(keys, function (key) {
        var root = find(key);
        if (!mergedNodes[root]) { mergedNodes[root] = nodes[root]; mergedAdj[root] = []; }
      });
      array.forEach(keys, function (key) {
        var root = find(key);
        array.forEach(adj[key] || [], function (edge) {
          var toRoot = find(edge.to);
          if (toRoot === root) return; // self-loop from merge — discard
          mergedAdj[root].push({ to: toRoot, dist: edge.dist, road: edge.road, coords: edge.coords });
        });
      });

      this.networkGraph = { nodes: mergedNodes, adj: mergedAdj };
    },

    _buildNodeGrid: function () {
      var GRID_CELL_DEG = 0.02; // ~2km cells
      this._gridCellDeg = GRID_CELL_DEG;
      var nodes = this.networkGraph.nodes;
      var grid = {};
      var minCx = Infinity, maxCx = -Infinity, minCy = Infinity, maxCy = -Infinity;

      for (var key in nodes) {
        if (!nodes.hasOwnProperty(key)) continue;
        var lng = nodes[key][0], lat = nodes[key][1];
        var cx = Math.floor(lng / GRID_CELL_DEG);
        var cy = Math.floor(lat / GRID_CELL_DEG);
        var cellKey = cx + ',' + cy;
        if (!grid[cellKey]) grid[cellKey] = [];
        grid[cellKey].push(key);
        if (cx < minCx) minCx = cx;
        if (cx > maxCx) maxCx = cx;
        if (cy < minCy) minCy = cy;
        if (cy > maxCy) maxCy = cy;
      }

      this.nodeGrid = grid;
      var keyCount = 0;
      for (var kk in grid) { if (grid.hasOwnProperty(kk)) keyCount++; }
      this.nodeGridMaxRadius = keyCount > 0 ? Math.max(maxCx - minCx, maxCy - minCy, 0) + 1 : 0;
    },

    _findClosestGraphNode: function (targetCoord) {
      if (!this.nodeGrid) return null;
      var nodes = this.networkGraph.nodes;
      var grid = this.nodeGrid;
      var GRID_CELL_DEG = this._gridCellDeg;
      var lng = targetCoord[0], lat = targetCoord[1];
      var cx = Math.floor(lng / GRID_CELL_DEG);
      var cy = Math.floor(lat / GRID_CELL_DEG);

      var minVal = Infinity, closestKey = null;

      function scanRing(radius) {
        for (var dx = -radius; dx <= radius; dx++) {
          for (var dy = -radius; dy <= radius; dy++) {
            if (Math.max(Math.abs(dx), Math.abs(dy)) !== radius) continue;
            var bucket = grid[(cx + dx) + ',' + (cy + dy)];
            if (!bucket) continue;
            for (var i = 0; i < bucket.length; i++) {
              var key = bucket[i];
              var d = haversineKm(lng, lat, nodes[key][0], nodes[key][1]);
              if (d < minVal) { minVal = d; closestKey = key; }
            }
          }
        }
      }

      var radius = 0, foundAtRadius = -1;
      while (radius <= this.nodeGridMaxRadius) {
        scanRing(radius);
        if (closestKey !== null && foundAtRadius === -1) foundAtRadius = radius;
        if (foundAtRadius !== -1 && radius >= foundAtRadius + 1) break;
        radius++;
      }
      return closestKey;
    },

    _runDijkstra: function (startKey, targetKey, edgePenalty) {
      var graph = this.networkGraph;
      var costs = {}, previous = {}, visited = {};
      costs[startKey] = 0;

      var heap = new MinHeap();
      heap.push(0, startKey);

      while (heap.size() > 0) {
        var top = heap.pop();
        var cost = top[0], current = top[1];
        if (visited[current]) continue;
        visited[current] = true;

        if (current === targetKey) break;

        var edges = graph.adj[current] || [];
        for (var i = 0; i < edges.length; i++) {
          var edge = edges[i];
          if (visited[edge.to]) continue;
          var penalty = edgePenalty ? (edgePenalty[edgeId(current, edge.to)] || 1) : 1;
          var altCost = cost + edge.dist * penalty;
          if (altCost < (costs[edge.to] === undefined ? Infinity : costs[edge.to])) {
            costs[edge.to] = altCost;
            previous[edge.to] = { from: current, road: edge.road, coords: edge.coords, dist: edge.dist };
            heap.push(altCost, edge.to);
          }
        }
      }

      if (costs[targetKey] === undefined) return null;

      var pathEdges = [];
      var nodeKeys = [targetKey];
      var curr = targetKey;
      var realDistance = 0;
      while (previous[curr] !== undefined && previous[curr] !== null) {
        pathEdges.unshift(previous[curr]);
        realDistance += previous[curr].dist;
        curr = previous[curr].from;
        nodeKeys.unshift(curr);
      }

      return { totalDistance: realDistance, edges: pathEdges, nodeKeys: nodeKeys };
    },

    _edgeOverlapRatio: function (pathA, pathB) {
      var setA = {}, sizeA = 0;
      for (var i = 0; i < pathA.nodeKeys.length - 1; i++) {
        setA[edgeId(pathA.nodeKeys[i], pathA.nodeKeys[i + 1])] = true;
        sizeA++;
      }
      var shared = 0;
      var sizeB = pathB.nodeKeys.length - 1;
      for (var j = 0; j < sizeB; j++) {
        if (setA[edgeId(pathB.nodeKeys[j], pathB.nodeKeys[j + 1])]) shared++;
      }
      var minLen = Math.min(sizeA, sizeB);
      return minLen === 0 ? 1 : shared / minLen;
    },

    _computeRouteAlternatives: function (startKey, targetKey, maxAlternatives) {
      var primary = this._runDijkstra(startKey, targetKey, null);
      if (!primary) return [];

      var results = [primary];
      var penalty = {};
      var self = this;

      function applyPenalty(path, factor) {
        for (var i = 0; i < path.nodeKeys.length - 1; i++) {
          var id = edgeId(path.nodeKeys[i], path.nodeKeys[i + 1]);
          penalty[id] = (penalty[id] || 1) * factor;
        }
      }

      applyPenalty(primary, 6);

      for (var i = 1; i < maxAlternatives; i++) {
        var candidate = this._runDijkstra(startKey, targetKey, penalty);
        if (!candidate) break;

        var isDuplicate = false;
        for (var j = 0; j < results.length; j++) {
          if (self._edgeOverlapRatio(results[j], candidate) > 0.85) { isDuplicate = true; break; }
        }
        if (!isDuplicate) results.push(candidate);
        applyPenalty(candidate, 6);
      }

      results.sort(function (a, b) { return a.totalDistance - b.totalDistance; });
      return results;
    },

    _snapPointToNetwork: function (pt) {
      var best = null;
      var segments = this._routeCoordSegments;
      for (var i = 0; i < segments.length; i++) {
        var seg = segments[i];
        var proj = projectPointOnSegment(seg[0], seg[1], pt);
        var d = haversineKm(pt[0], pt[1], proj.point[0], proj.point[1]);
        if (!best || d < best.distKm) best = { coordinates: proj.point, distKm: d };
      }
      return best;
    },

    // ====================================================================
    // WAYPOINT SELECTION UI
    // ====================================================================
    _isDepArrSelectable: function (wp) {
      var types = this.config.depArrTypes || [];
      var lowerType = String(wp.type || '').toLowerCase();
      for (var i = 0; i < types.length; i++) {
        if (String(types[i]).toLowerCase() === lowerType) return true;
      }
      return false;
    },

    _onDepInputClick: function (evt) {
      evt.stopPropagation();
      this._renderComboList(this.depList, this.depInput.value, lang.hitch(this, this._selectDepWaypoint));
    },
    _onArrInputClick: function (evt) {
      evt.stopPropagation();
      this._renderComboList(this.arrList, this.arrInput.value, lang.hitch(this, this._selectArrWaypoint));
    },
    _onDepInputKeyUp: function () {
      this._renderComboList(this.depList, this.depInput.value, lang.hitch(this, this._selectDepWaypoint));
    },
    _onArrInputKeyUp: function () {
      this._renderComboList(this.arrList, this.arrInput.value, lang.hitch(this, this._selectArrWaypoint));
    },
    _onDocumentClick: function () {
      domClass.remove(this.depList, 'rp-open');
      domClass.remove(this.arrList, 'rp-open');
    },

    _renderComboList: function (listNode, searchText, onSelect) {
      var self = this;
      var lowerSearch = String(searchText || '').trim().toLowerCase();
      var candidates = array.filter(this.waypoints, function (wp) { return self._isDepArrSelectable(wp); });
      if (lowerSearch) {
        candidates = array.filter(candidates, function (wp) {
          return String(wp.name || '').toLowerCase().indexOf(lowerSearch) !== -1;
        });
      }
      candidates = candidates.slice(0, 50);

      listNode.innerHTML = '';
      if (candidates.length === 0) {
        domConstruct.create('div', { className: 'rp-combo-empty', innerHTML: 'No matching waypoints' }, listNode);
      } else {
        array.forEach(candidates, function (wp) {
          var item = domConstruct.create('div', { className: 'rp-combo-item' }, listNode);
          domConstruct.create('span', { innerHTML: escapeHtml(wp.name) }, item);
          domConstruct.create('span', { className: 'rp-combo-item-type', innerHTML: escapeHtml(wp.type) }, item);
          on(item, 'click', function (evt) {
            evt.stopPropagation();
            onSelect(wp);
            domClass.remove(listNode, 'rp-open');
          });
        });
      }
      domClass.add(listNode, 'rp-open');
    },

    _selectDepWaypoint: function (wp) {
      this.selectedDepWp = wp;
      this.depInput.value = wp.name;
      this._checkReadyToCalculate();
    },
    _selectArrWaypoint: function (wp) {
      this.selectedArrWp = wp;
      this.arrInput.value = wp.name;
      this._checkReadyToCalculate();
    },

    _validateTolerance: function () {
      var min = this.config.toleranceMinMeters || 10;
      var max = this.config.toleranceMaxMeters || 5000;
      var val = parseFloat(this.toleranceInput.value);
      if (!isFinite(val)) val = this.config.defaultToleranceMeters || 300;
      var clamped = Math.min(Math.max(val, min), max);
      if (clamped !== val) {
        this.toleranceInput.value = clamped;
        this.toleranceHintNode.innerHTML = 'Clamped to valid range (' + min + '-' + max + 'm).';
        domClass.add(this.toleranceHintNode, 'rp-warn');
      } else {
        this.toleranceHintNode.innerHTML = '';
        domClass.remove(this.toleranceHintNode, 'rp-warn');
      }
      return clamped;
    },

    _checkReadyToCalculate: function () {
      var ready = this._routesReady && this._waypointsReady &&
        this.selectedDepWp && this.selectedArrWp &&
        this.selectedDepWp.id !== this.selectedArrWp.id;
      this.calcBtn.disabled = !ready;
    },

    // ====================================================================
    // CALCULATE PIPELINE
    // ====================================================================
    onCalculateClick: function () {
      var depWp = this.selectedDepWp, arrWp = this.selectedArrWp;
      if (!depWp || !arrWp) return;

      var toleranceMeters = this._validateTolerance();
      var toleranceKm = toleranceMeters / 1000.0;

      var avgSpeedKmh = parseFloat(this.speedInput.value);
      if (!isFinite(avgSpeedKmh) || avgSpeedKmh <= 0) {
        this._showSummaryError('Invalid Average Speed', 'Enter a positive number of km/h before calculating.');
        return;
      }

      this._showLoading('Calculating route…');
      var self = this;
      setTimeout(function () {
        try {
          self._runCalculate(depWp, arrWp, toleranceKm, avgSpeedKmh);
        } finally {
          self._hideLoading();
        }
      }, 0);
    },

    _runCalculate: function (depWp, arrWp, toleranceKm, avgSpeedKmh) {
      var depPt = [depWp.lng, depWp.lat];
      var arrPt = [arrWp.lng, arrWp.lat];

      var snappedDep = this._snapPointToNetwork(depPt);
      var snappedArr = this._snapPointToNetwork(arrPt);

      if (!snappedDep || !snappedArr) {
        this._showSummaryError('Route Unreachable', 'No route network was found near the selected waypoints.');
        this._clearRouteDisplay();
        return;
      }

      var depConnectorDist = haversineKm(depPt[0], depPt[1], snappedDep.coordinates[0], snappedDep.coordinates[1]);
      var arrConnectorDist = haversineKm(arrPt[0], arrPt[1], snappedArr.coordinates[0], snappedArr.coordinates[1]);

      var startKey = this._findClosestGraphNode(snappedDep.coordinates);
      var targetKey = this._findClosestGraphNode(snappedArr.coordinates);

      var pathAlternatives = (startKey && targetKey)
        ? this._computeRouteAlternatives(startKey, targetKey, this.config.maxRouteAlternatives || 3)
        : [];

      if (pathAlternatives.length === 0) {
        this._showSummaryError('Route Unreachable', 'No continuous network route found between the selected waypoints.');
        this._clearRouteDisplay();
        return;
      }

      var self = this;
      var routeAlternatives = array.map(pathAlternatives, function (networkPath) {
        return self._buildFullRouteResult(networkPath, depWp, arrWp, snappedDep, snappedArr,
          depConnectorDist, arrConnectorDist, toleranceKm, avgSpeedKmh);
      });

      this._selectRouteAlternative(routeAlternatives, 0);
    },

    _clearRouteDisplay: function () {
      if (this.routeLayerGroup) this.routeLayerGroup.clearLayers();
      this._setBaseWaypointsDimmed(false);
      this.optionsNode.style.display = 'none';
      this.schematicSection.style.display = 'none';
      this.schematicNode.innerHTML = '';
      this._resetTable();
    },

    _showSummaryError: function (title, msg) {
      this.summaryNode.style.display = 'block';
      this.summaryNode.innerHTML =
        '<div class="rp-alert rp-alert-error"><strong>' + escapeHtml(title) + '</strong><br/>' + escapeHtml(msg) + '</div>';
      this.optionsNode.style.display = 'none';
    },

    _buildFullRouteResult: function (networkPath, depWp, arrWp, snappedDep, snappedArr,
      depConnectorDist, arrConnectorDist, toleranceKm, avgSpeedKmh) {

      var routeCoords = [];
      array.forEach(networkPath.edges, function (edge, idx) {
        if (idx === 0) routeCoords.push(edge.coords[0]);
        routeCoords.push(edge.coords[1]);
      });

      var detectedWaypoints = [];
      array.forEach(this.waypoints, function (wp) {
        if (wp.id === depWp.id || wp.id === arrWp.id) return;
        if (wp.lng == null || wp.lat == null) return;

        var snapped = nearestPointOnLineCoords(routeCoords, [wp.lng, wp.lat]);
        if (snapped && snapped.distKm <= toleranceKm) {
          detectedWaypoints.push({
            wp: wp,
            locationKm: snapped.location,
            distFromRouteKm: snapped.distKm,
            snappedCoords: snapped.coordinates
          });
        }
      });
      detectedWaypoints.sort(function (a, b) { return a.locationKm - b.locationKm; });

      var totalDist = depConnectorDist + networkPath.totalDistance + arrConnectorDist;

      var result = {
        depWp: depWp, arrWp: arrWp,
        snappedDep: snappedDep, snappedArr: snappedArr,
        depConnectorDist: depConnectorDist, arrConnectorDist: arrConnectorDist,
        networkPath: networkPath,
        routeCoords: routeCoords,
        detectedWaypoints: detectedWaypoints,
        totalDist: totalDist,
        avgSpeedKmh: avgSpeedKmh
      };
      result.sequenceData = this._buildRouteSequenceData(result);
      return result;
    },

    _buildRouteSequenceData: function (res) {
      var items = [];
      var seqIndex = 1;
      var outboundCum = 0;

      items.push({
        seq: seqIndex++, type: 'Start',
        desc: 'Departure (A): ' + res.depWp.name + ' [ID: ' + res.depWp.id + ']',
        shortName: res.depWp.name, isKissPoint: res.depWp.isKissPoint,
        lat: res.depWp.lat, lng: res.depWp.lng,
        outboundLeg: 0, outboundCum: 0
      });

      if (res.depConnectorDist > 0.001) {
        outboundCum += res.depConnectorDist;
        items.push({
          seq: seqIndex++, type: 'Connector', desc: 'Link to Network Line', shortName: 'Link',
          isKissPoint: false, outboundLeg: res.depConnectorDist, outboundCum: outboundCum
        });
      }

      var lastLocationKm = 0;
      array.forEach(res.detectedWaypoints, function (item, idx) {
        var legDist = item.locationKm - lastLocationKm;
        outboundCum += legDist;
        lastLocationKm = item.locationKm;

        items.push({
          seq: seqIndex++,
          type: item.wp.isKissPoint ? 'Vehicle Swap Point' : 'Pass-Through WP',
          desc: 'Stop #' + (idx + 1) + ': ' + item.wp.name + ' [ID: ' + item.wp.id + ']' + (item.wp.isKissPoint ? ' ⇄' : ''),
          shortName: item.wp.name, isKissPoint: item.wp.isKissPoint,
          lat: item.wp.lat, lng: item.wp.lng,
          outboundLeg: legDist, outboundCum: outboundCum
        });
      });

      var remainingCorridorDist = res.networkPath.totalDistance - lastLocationKm;
      if (res.arrConnectorDist > 0.001) {
        outboundCum += remainingCorridorDist;
        items.push({
          seq: seqIndex++, type: 'Connector', desc: 'Link to Arrival Point', shortName: 'Link',
          isKissPoint: false, outboundLeg: res.arrConnectorDist, outboundCum: outboundCum + res.arrConnectorDist
        });
      }

      items.push({
        seq: seqIndex++, type: 'Finish',
        desc: 'Arrival (B): ' + res.arrWp.name + ' [ID: ' + res.arrWp.id + ']',
        shortName: res.arrWp.name, isKissPoint: res.arrWp.isKissPoint,
        lat: res.arrWp.lat, lng: res.arrWp.lng,
        outboundLeg: 0, outboundCum: res.totalDist
      });

      var totalRouteDist = res.totalDist;
      array.forEach(items, function (item) { item.returnCum = totalRouteDist - item.outboundCum; });

      for (var i = 0; i < items.length; i++) {
        var itemLeg = 0;
        if (i < items.length - 1) itemLeg = items[i + 1].returnCum - items[i].returnCum;
        items[i].returnLeg = Math.abs(itemLeg);
      }

      var speed = res.avgSpeedKmh;
      array.forEach(items, function (item) {
        item.outboundTimeHrs = speed > 0 ? item.outboundCum / speed : null;
        item.returnTimeHrs = speed > 0 ? item.returnCum / speed : null;
      });

      return items;
    },

    _selectRouteAlternative: function (routeAlternatives, index) {
      var result = routeAlternatives[index];
      result.routeAlternatives = routeAlternatives;
      result.selectedAlternativeIndex = index;
      this.lastCalculatedRoute = result;

      this._renderSummaryCard(result);
      this._renderTableBreakdown(result);
      this._renderSchematicDiagram(result);
      this._renderRouteOptionsUI(result);
      this._renderRouteOnMap(result);

      this.exportBtn.disabled = false;
    },

    // ====================================================================
    // RENDERING — SIDEBAR
    // ====================================================================
    _renderSummaryCard: function (res) {
      var swapCount = 0;
      array.forEach(res.detectedWaypoints, function (w) { if (w.wp.isKissPoint) swapCount++; });

      var html = '<div class="rp-metric-grid">' +
        '<div class="rp-metric"><div class="rp-metric-val">' + res.totalDist.toFixed(2) + ' km</div>' +
        '<div class="rp-metric-lbl">Total Distance</div></div>' +
        '<div class="rp-metric"><div class="rp-metric-val">' + res.detectedWaypoints.length + '</div>' +
        '<div class="rp-metric-lbl">En-route Stops</div></div>' +
        '<div class="rp-metric rp-metric-wide"><div class="rp-metric-val">' +
        formatDuration(res.totalDist / res.avgSpeedKmh) + '</div>' +
        '<div class="rp-metric-lbl">Est. Travel Time (' + res.avgSpeedKmh + ' km/h)</div></div>' +
        '</div>';

      if (swapCount > 0) {
        html += '<div class="rp-swap-note">&#8644; ' + swapCount + ' Vehicle Swap Point(s) Included</div>';
      }

      this.summaryNode.style.display = 'block';
      this.summaryNode.innerHTML = html;
    },

    _renderRouteOptionsUI: function (res) {
      var alternatives = res.routeAlternatives;
      if (!alternatives || alternatives.length < 2) {
        this.optionsNode.style.display = 'none';
        this.optionsNode.innerHTML = '';
        return;
      }

      var shortestDist = alternatives[0].totalDist;
      var self = this;
      var html = '<div class="rp-section-title">Route Options</div><div class="rp-options-list">';
      array.forEach(alternatives, function (alt, idx) {
        var isSelected = idx === res.selectedAlternativeIndex;
        var diff = alt.totalDist - shortestDist;
        html += '<div class="rp-option' + (isSelected ? ' rp-selected' : '') + '" data-idx="' + idx + '">' +
          '<div class="rp-option-label">Option ' + (idx + 1) + (idx === 0 ? ' · Shortest' : '') + '</div>' +
          '<div class="rp-option-meta"><span>' + alt.totalDist.toFixed(1) + ' km</span>' +
          '<span>' + alt.detectedWaypoints.length + ' stops</span>' +
          (idx > 0 ? '<span class="rp-option-diff">+' + diff.toFixed(1) + ' km</span>' : '') +
          '</div></div>';
      });
      html += '</div>';

      this.optionsNode.style.display = 'block';
      this.optionsNode.innerHTML = html;

      array.forEach(this.optionsNode.querySelectorAll('.rp-option'), function (el) {
        on(el, 'click', function () {
          self._selectRouteAlternative(alternatives, parseInt(el.getAttribute('data-idx'), 10));
        });
      });
    },

    // Waypoint-only "directions" — no turn-by-turn, just the stop sequence
    // with distance and time-to-reach, and kiss points visually flagged.
    _renderSchematicDiagram: function (res) {
      var items = res.sequenceData;
      var html = '';
      array.forEach(items, function (item, idx) {
        var isStart = item.type === 'Start';
        var isFinish = item.type === 'Finish';
        var isKiss = item.isKissPoint;

        var symbolClass = 'rp-schem-symbol';
        var iconText = idx;
        if (isStart) { symbolClass += ' is-dep'; iconText = 'A'; }
        else if (isFinish) { symbolClass += ' is-arr'; iconText = 'B'; }
        else if (isKiss) { symbolClass += ' is-kiss'; iconText = '⇄'; }
        else { symbolClass += ' is-wp'; }

        html += '<div class="rp-schem-node">' +
          '<div class="' + symbolClass + '">' + iconText + '</div>' +
          '<div class="rp-schem-label" title="' + escapeHtml(item.shortName) + '">' + escapeHtml(item.shortName) + '</div>' +
          '<div class="rp-schem-dist">' + item.outboundCum.toFixed(1) + ' km &middot; ' + formatDuration(item.outboundTimeHrs) + '</div>' +
          '</div>';
      });

      this.schematicSection.style.display = 'block';
      this.schematicNode.innerHTML = html;
    },

    _resetTable: function () {
      this.tableBody.innerHTML = '<tr><td colspan="9" class="rp-empty-row">Calculate a route to view the manifest.</td></tr>';
      this.exportBtn.disabled = true;
    },

    _renderTableBreakdown: function (res) {
      var items = res.sequenceData;
      var typeColors = {
        'Start': '#0284c7', 'Finish': '#dc2626', 'Vehicle Swap Point': '#d97706',
        'Pass-Through WP': '#94a3b8', 'Connector': '#d97706'
      };
      var html = '';
      array.forEach(items, function (item) {
        var color = typeColors[item.type] || '#0284c7';
        html += '<tr>' +
          '<td>' + item.seq + '</td>' +
          '<td><span style="color:' + color + ';font-weight:bold;">' + escapeHtml(item.type) + '</span></td>' +
          '<td>' + escapeHtml(item.desc) + '</td>' +
          '<td>' + (item.outboundLeg > 0 ? item.outboundLeg.toFixed(3) + ' km' : '-') + '</td>' +
          '<td><strong>' + item.outboundCum.toFixed(3) + ' km</strong></td>' +
          '<td>' + formatDuration(item.outboundTimeHrs) + '</td>' +
          '<td class="rp-ret-col">' + (item.returnLeg > 0 ? item.returnLeg.toFixed(3) + ' km' : '-') + '</td>' +
          '<td class="rp-ret-col"><strong>' + item.returnCum.toFixed(3) + ' km</strong></td>' +
          '<td class="rp-ret-col">' + formatDuration(item.returnTimeHrs) + '</td>' +
          '</tr>';
      });
      this.tableBody.innerHTML = html;
      this.exportBtn.disabled = false;
    },

    // ====================================================================
    // RENDERING — LEAFLET MAP
    // ====================================================================
    _renderRouteOnMap: function (res) {
      if (!this.leafletMap) return;
      var L = window.L;
      this.routeLayerGroup.clearLayers();
      this._setBaseWaypointsDimmed(true);

      var depSnap = res.snappedDep.coordinates;
      var arrSnap = res.snappedArr.coordinates;

      var connectorStyle = { color: '#d97706', weight: 3, dashArray: '5, 5', opacity: 0.9 };
      L.polyline([
        [res.depWp.lat, res.depWp.lng],
        [depSnap[1], depSnap[0]]
      ], connectorStyle).addTo(this.routeLayerGroup);
      L.polyline([
        [arrSnap[1], arrSnap[0]],
        [res.arrWp.lat, res.arrWp.lng]
      ], connectorStyle).addTo(this.routeLayerGroup);

      L.polyline(
        array.map(res.routeCoords, function (c) { return [c[1], c[0]]; }),
        { color: '#0284c7', weight: 5, opacity: 0.9, lineCap: 'round' }
      ).addTo(this.routeLayerGroup);

      var self = this;
      array.forEach(res.detectedWaypoints, function (item, idx) {
        var isKiss = item.wp.isKissPoint;
        var icon = isKiss ? self._leafletIcon('kiss') : self._leafletIcon('num', { color: '#94a3b8', label: idx + 1 });
        var marker = L.marker([item.wp.lat, item.wp.lng], { icon: icon }).addTo(self.routeLayerGroup);
        var cum = (res.depConnectorDist + item.locationKm).toFixed(1);
        marker.bindTooltip(
          '<strong>' + escapeHtml(item.wp.name) + '</strong> (' + cum + ' km)',
          { permanent: isKiss, direction: 'top', offset: [0, -12], className: 'rp-map-tooltip' }
        );
        marker.bindPopup(
          '<strong>Stop #' + (idx + 1) + ': ' + escapeHtml(item.wp.name) + '</strong><br/>' +
          (isKiss ? '<span style="color:#d97706;font-weight:bold;">&#8644; Vehicle Swap Point</span><br/>' : '') +
          'Cumulative Dist: ' + cum + ' km'
        );
      });

      L.marker([res.depWp.lat, res.depWp.lng], { icon: this._leafletIcon('endpoint', { color: '#0284c7', label: 'A' }) })
        .addTo(this.routeLayerGroup)
        .bindTooltip('<strong>A: ' + escapeHtml(res.depWp.name) + '</strong>', { permanent: true, direction: 'top', offset: [0, -22], className: 'rp-map-tooltip' });
      L.marker([res.arrWp.lat, res.arrWp.lng], { icon: this._leafletIcon('endpoint', { color: '#dc2626', label: 'B' }) })
        .addTo(this.routeLayerGroup)
        .bindTooltip('<strong>B: ' + escapeHtml(res.arrWp.name) + '</strong>', { permanent: true, direction: 'top', offset: [0, -22], className: 'rp-map-tooltip' });

      var bounds = L.latLngBounds(array.map(res.routeCoords, function (c) { return [c[1], c[0]]; }));
      bounds.extend([res.depWp.lat, res.depWp.lng]);
      bounds.extend([res.arrWp.lat, res.arrWp.lng]);
      this.leafletMap.fitBounds(bounds, { padding: [30, 30] });
    },

    // ====================================================================
    // ADD WAYPOINT TOOL
    // ====================================================================
    _onToggleAddWaypoint: function () {
      this._setAddingMode(!this._isAddingWaypoint);
    },

    _setAddingMode: function (active) {
      this._isAddingWaypoint = active;
      domClass.toggle(this.addWaypointBtn, 'rp-active', active);
      this.addWaypointBtn.innerHTML = active ? 'Cancel Adding Waypoint' : '&#10010; Add Waypoint on Map';
      this.mapHintNode.style.display = active ? 'block' : 'none';
      if (this.leafletMap) {
        this.leafletMap.getContainer().style.cursor = active ? 'crosshair' : '';
      }
      if (!active && this._pendingWaypointMarker) {
        this.leafletMap.removeLayer(this._pendingWaypointMarker);
        this._pendingWaypointMarker = null;
      }
    },

    _onMapClick: function (e) {
      if (!this._isAddingWaypoint) return;
      if (this._pendingWaypointMarker) {
        this.leafletMap.removeLayer(this._pendingWaypointMarker);
        this._pendingWaypointMarker = null;
      }
      this._openAddWaypointForm(e.latlng);
    },

    _openAddWaypointForm: function (latlng) {
      var L = window.L;
      var self = this;
      var marker = L.marker(latlng, { icon: this._leafletIcon('new'), draggable: true }).addTo(this.leafletMap);
      this._pendingWaypointMarker = marker;

      var knownTypes = [];
      array.forEach(this.waypoints, function (wp) {
        if (wp.type && array.indexOf(knownTypes, wp.type) === -1) knownTypes.push(wp.type);
      });

      var form = domConstruct.create('div', { className: 'rp-popup-form' });
      domConstruct.create('label', { innerHTML: 'Name' }, form);
      var nameInput = domConstruct.create('input', { type: 'text', placeholder: 'Waypoint name' }, form);

      domConstruct.create('label', { innerHTML: 'Type' }, form);
      var typeListId = 'rp-type-list-' + this.id;
      var typeInput = domConstruct.create('input', { type: 'text', placeholder: 'e.g. Coordination, Site...' }, form);
      typeInput.setAttribute('list', typeListId);
      var datalist = domConstruct.create('datalist', { id: typeListId }, form);
      array.forEach(knownTypes, function (t) { domConstruct.create('option', { value: t }, datalist); });

      var kissCheckId = 'rp-kiss-' + this.id + '-' + Date.now();
      var checkRow = domConstruct.create('div', { className: 'rp-popup-check' }, form);
      var kissCheck = domConstruct.create('input', { type: 'checkbox', id: kissCheckId }, checkRow);
      var kissLabel = domConstruct.create('label', {
        innerHTML: 'Vehicle Swap / Kiss Point',
        style: { margin: 0, textTransform: 'none', fontSize: '11.5px' }
      }, checkRow);
      kissLabel.setAttribute('for', kissCheckId);

      var errorNode = domConstruct.create('div', { className: 'rp-popup-error' }, form);

      var btnRow = domConstruct.create('div', { className: 'rp-popup-btn-row' }, form);
      var saveBtn = domConstruct.create('button', { className: 'rp-btn rp-btn-primary rp-btn-sm', innerHTML: 'Save' }, btnRow);
      var cancelBtn = domConstruct.create('button', { className: 'rp-btn rp-btn-secondary rp-btn-sm', innerHTML: 'Cancel' }, btnRow);

      var saved = false;

      on(saveBtn, 'click', function () {
        var name = nameInput.value.trim();
        if (!name) { errorNode.innerHTML = 'Name is required.'; return; }
        saveBtn.disabled = true;
        errorNode.innerHTML = '';
        self._saveNewWaypoint(marker.getLatLng(), name, typeInput.value.trim(), !!kissCheck.checked)
          .then(function () {
            saved = true;
            marker.closePopup();
            self.leafletMap.removeLayer(marker);
            self._pendingWaypointMarker = null;
            self._setAddingMode(false);
          }, function (err) {
            saveBtn.disabled = false;
            errorNode.innerHTML = 'Save failed: ' + escapeHtml(err && err.message || err);
          });
      });

      on(cancelBtn, 'click', function () {
        marker.closePopup();
      });

      marker.bindPopup(form, { closeOnClick: false, minWidth: 230 }).openPopup();
      marker.on('popupclose', function () {
        if (!saved && self._pendingWaypointMarker === marker) {
          self.leafletMap.removeLayer(marker);
          self._pendingWaypointMarker = null;
        }
      });
      marker.on('dragend', function () { /* position read fresh from marker.getLatLng() on save */ });
    },

    // Uses a detached esri/layers/FeatureLayer purely for its applyEdits()
    // call — it's never added to any map, just used to talk to the REST
    // endpoint once its metadata (fields/capabilities) has loaded.
    _getWaypointsEditLayer: function () {
      var deferred = new Deferred();
      if (!this._waypointsLayerUrl) {
        deferred.reject(new Error('Waypoints layer URL not resolved yet.'));
        return deferred.promise;
      }
      if (this._waypointsEditLayer && this._waypointsEditLayer.loaded) {
        deferred.resolve(this._waypointsEditLayer);
        return deferred.promise;
      }
      if (!this._waypointsEditLayer) {
        this._waypointsEditLayer = new FeatureLayer(this._waypointsLayerUrl, { mode: FeatureLayer.MODE_ONDEMAND });
      }
      var layerRef = this._waypointsEditLayer;
      on.once(layerRef, 'load', function () { deferred.resolve(layerRef); });
      on.once(layerRef, 'error', function (err) { deferred.reject(err); });
      return deferred.promise;
    },

    _saveNewWaypoint: function (latlng, name, typeVal, isKiss) {
      var deferred = new Deferred();
      var self = this;
      var fields = this.config.waypointFields || {};

      this._showLoading('Saving waypoint…');
      this._getWaypointsEditLayer().then(function (layer) {
        var attrs = {};
        attrs[fields.nameField || 'name'] = name;
        attrs[fields.typeField || 'type'] = typeVal || '';
        attrs[fields.kissPointField || 'kisspoint'] = isKiss
          ? (self.config.kissPointWriteTrueValue || 'Yes')
          : (self.config.kissPointWriteFalseValue || 'No');

        var geometry = new EsriPoint(latlng.lng, latlng.lat, new SpatialReference({ wkid: 4326 }));
        var graphic = new Graphic(geometry, null, attrs);

        layer.applyEdits([graphic], null, null, function (addResults) {
          self._hideLoading();
          var result = addResults && addResults[0];
          if (!result || !result.success) {
            var msg = (result && result.error && result.error.description) || 'Server rejected the edit.';
            self._showToast('Failed to save waypoint: ' + msg, true);
            deferred.reject(new Error(msg));
            return;
          }

          var idField = fields.idField || 'fid';
          var newWp = {
            id: result.objectId,
            name: name,
            type: typeVal || '',
            isKissPoint: isKiss,
            lng: latlng.lng,
            lat: latlng.lat
          };
          newWp.id = result.objectId != null ? result.objectId : ('new-' + Date.now());
          self.waypoints.push(newWp);
          self._renderBaseWaypointsLayer();
          self._showToast('Waypoint "' + name + '" saved.', false);
          deferred.resolve(newWp);
        }, function (err) {
          self._hideLoading();
          self._showToast('Failed to save waypoint: ' + (err && err.message || err), true);
          deferred.reject(err);
        });
      }, function (err) {
        self._hideLoading();
        self._showToast('Could not reach Waypoints layer for editing: ' + (err && err.message || err), true);
        deferred.reject(err);
      });

      return deferred.promise;
    },

    // ====================================================================
    // RESET / EXPORT
    // ====================================================================
    onResetClick: function () {
      this.selectedDepWp = null;
      this.selectedArrWp = null;
      this.depInput.value = '';
      this.arrInput.value = '';
      this.lastCalculatedRoute = null;

      if (this.routeLayerGroup) this.routeLayerGroup.clearLayers();
      this._setBaseWaypointsDimmed(false);
      this.summaryNode.style.display = 'none';
      this.summaryNode.innerHTML = '';
      this.optionsNode.style.display = 'none';
      this.optionsNode.innerHTML = '';
      this.schematicSection.style.display = 'none';
      this.schematicNode.innerHTML = '';
      this._resetTable();
      this._checkReadyToCalculate();
    },

    onExportCsvClick: function () {
      if (!this.lastCalculatedRoute) return;
      var items = this.lastCalculatedRoute.sequenceData;

      var csv = 'Seq,Type,Vehicle_Swap_Point,Waypoint_Name_Segment,Coordinates_Lat_Lng,' +
        'Outbound_Leg_km,Outbound_Cum_Dist_km,Outbound_Time_to_Reach,' +
        'Return_Leg_km,Return_Cum_Dist_km,Return_Time\n';

      array.forEach(items, function (item) {
        csv += item.seq + ',"' + item.type + '","' + (item.isKissPoint ? 'Yes' : 'No') + '","' +
          String(item.desc).replace(/"/g, '""') + '","' + formatCoords(item.lat, item.lng) + '",' +
          item.outboundLeg.toFixed(4) + ',' + item.outboundCum.toFixed(4) + ',"' + formatDuration(item.outboundTimeHrs) + '",' +
          item.returnLeg.toFixed(4) + ',' + item.returnCum.toFixed(4) + ',"' + formatDuration(item.returnTimeHrs) + '"\n';
      });

      var blob = new Blob([csv], { type: 'text/csv' });
      var url = window.URL.createObjectURL(blob);
      var a = document.createElement('a');
      a.href = url;
      a.download = 'route_manifest.csv';
      document.body.appendChild(a);
      a.click();
      document.body.removeChild(a);
      window.URL.revokeObjectURL(url);
    }

  });
});
