/* Parcel Reference Prices — app logic (requires the ArcGIS Maps SDK 4.28 script loaded first) */
/* =====================================================================
   CONFIG
   ===================================================================== */

const WEBMAP_ID  = "cb6527b01be144508312d75d37f21326";
const PORTAL_URL = "https://gh.space.gov.rw/portal";

// Per-year village layer + rate fields. The FIRST year is the left side of the swipe,
// the SECOND year is the right side. Titles match ignoring case, spacing and dash type.
const YEARS = {
    "2021": { layerTitle:"Village - 2021 Prices", min:"price_21_min", mean:"price_21_mean", max:"price_21_max" },
    "2024": { layerTitle:"Village - 2024 Prices", min:"price_24_min", mean:"price_24_mean", max:"price_24_max" }
};
const DEFAULT_MODE = "2021";          // "2021", "2024" or "compare"

const VILLAGE_KEY_FIELD = "p_d_s_c_v_key";
const PARCEL_TITLE_RX   = /parcels\s*$/i;

const PARCEL_FIELDS = {
    province:"province", district:"district", sector:"sector",
    cell:"cell", village:"village", area:"size"
};

const AREA_TO_SQM = 1;                // 1 = size is m², 10000 = hectares
const CURRENCY    = "RWF";            // shown in the legend note
const UPI_FIELD   = "upi";

const PROVINCE_FIXES = {
    // "City of Kigali": "Kigali City",
};

const SCALE_LIMIT    = 6000;
const MAX_LABELS     = 400;           // per year
const RATE_PAGE_SIZE = 1000;
const RATE_PARALLEL  = 4;

/* =====================================================================
   APP
   ===================================================================== */
require([
    "esri/config","esri/WebMap","esri/views/MapView","esri/layers/GraphicsLayer",
    "esri/Graphic","esri/geometry/geometryEngine","esri/core/reactiveUtils",
    "esri/widgets/Home","esri/widgets/Search","esri/widgets/Legend",
    "esri/widgets/Expand","esri/widgets/Swipe"
], function(esriConfig, WebMap, MapView, GraphicsLayer, Graphic, geometryEngine, reactiveUtils,
            Home, Search, Legend, Expand, Swipe){

    esriConfig.portalUrl = PORTAL_URL;

    /* ---------- helpers ---------- */
    const KEY_PARTS = ["province","district","sector","cell","village"];
    const YEAR_LIST = Object.keys(YEARS);
    const $ = id => document.getElementById(id);

    function setHint(text, warn){
        const h = $("hint");
        h.textContent = text; h.title = text;
        h.classList.toggle("warn", !!warn);
    }
    function setOverlay(text){ const o = $("overlayText"); if (o) o.textContent = text; }

    const normText = s => (s == null ? "" : String(s))
        .normalize("NFD").replace(/[\u0300-\u036f]/g, "")
        .replace(/[\u2010-\u2015\u2212]/g, "-")
        .toLowerCase().replace(/\s+/g, " ").trim();
    const normKey = s => normText(s).replace(/\s*_\s*/g, "_");
    const PROV_FIX = new Map(Object.entries(PROVINCE_FIXES).map(([k, v]) => [normText(k), v]));

    const toNum = v => {
        if (v == null || v === "") return null;
        const n = typeof v === "number" ? v : parseFloat(String(v).replace(/,/g, ""));
        return Number.isFinite(n) ? n : null;
    };
    function money(v){
        if (v == null || !Number.isFinite(v)) return "—";
        if (v >= 1e9) return (Math.round(v / 1e8) / 10) + "B";
        if (v >= 1e6) return (Math.round(v / 1e5) / 10) + "M";
        if (v >= 1e3) return Math.round(v / 1e3) + "K";
        return String(Math.round(v));
    }
    const escapeHtml = s => String(s).replace(/[&<>"']/g, c =>
        ({ "&":"&amp;", "<":"&lt;", ">":"&gt;", '"':"&quot;", "'":"&#39;" }[c]));

    /* ---------- state ---------- */
    const webmap = new WebMap({ portalItem:{ id:WEBMAP_ID } });

    // One label layer per year, so the swipe can clip each year's labels separately.
    const labelLayers = {};
    YEAR_LIST.forEach(y => {
        labelLayers[y] = new GraphicsLayer({ listMode:"hide", legendEnabled:false, title:"Price labels " + y });
    });

    let view = null;
    let swipe = null, swipeWatch = null;
    let parcels = [];                 // [{ layer, lv, info }]
    let mode = DEFAULT_MODE;          // "2021" | "2024" | "compare"
    const ratesLoaded = {};           // year -> Map (once downloaded)
    const rateCache = {};             // year -> Promise<Map>
    let drawSeq = 0, drawTimer = null;
    const noMatchLogged = new Set();

    const shownYears = () => mode === "compare" ? YEAR_LIST.slice(0, 2) : [mode];

    function villageLayer(year){
        const want = normText(YEARS[year].layerTitle);
        return webmap.allLayers.find(l => normText(l.title) === want);
    }

    /* ---------- village rates ---------- */
    function getRates(year){
        if (!rateCache[year]) {
            rateCache[year] = fetchRates(year)
                .then(m => (ratesLoaded[year] = m))
                .catch(err => { delete rateCache[year]; throw err; });
        }
        return rateCache[year];
    }

    async function fetchRates(year){
        const y = YEARS[year];
        const vl = villageLayer(year);
        if (!vl) {
            console.error('Village layer "' + y.layerTitle + '" not found. Layer titles in this map:',
                webmap.allLayers.map(l => l.title).toArray());
            throw new Error('Village layer "' + y.layerTitle + '" not found');
        }
        await vl.load();
        if (typeof vl.queryObjectIds !== "function") {
            throw new Error('"' + vl.title + '" is not a queryable feature layer');
        }
        const field = name => {
            const f = vl.getField(name);
            if (!f) throw new Error('Field "' + name + '" not found on "' + vl.title + '"');
            return f.name;
        };
        const keyF = field(VILLAGE_KEY_FIELD), minF = field(y.min), meanF = field(y.mean), maxF = field(y.max);

        const ids = await vl.queryObjectIds({ where:"1=1" });
        const maxRec = vl.capabilities?.query?.maxRecordCount || RATE_PAGE_SIZE;
        const size = Math.max(1, Math.min(RATE_PAGE_SIZE, maxRec));
        const chunks = [];
        for (let i = 0; i < ids.length; i += size) chunks.push(ids.slice(i, i + size));

        const m = new Map();
        let next = 0, done = 0;
        async function worker(){
            while (next < chunks.length) {
                const chunk = chunks[next++];
                const res = await vl.queryFeatures({
                    objectIds:chunk, outFields:[keyF, minF, meanF, maxF], returnGeometry:false
                });
                for (const ft of res.features) {
                    const a = ft.attributes;
                    const k = normKey(a[keyF]);
                    if (k) m.set(k, { min:toNum(a[minF]), mean:toNum(a[meanF]), max:toNum(a[maxF]) });
                }
                done++;
                if (shownYears().includes(year)) {
                    setHint("Loading " + year + " rates… " + Math.round(done / chunks.length * 100) + "%");
                }
            }
        }
        await Promise.all(Array.from({ length:Math.min(RATE_PARALLEL, chunks.length) }, worker));

        console.info("[rates " + year + "] " + m.size + " village keys cached from " + ids.length + " rows");
        if (m.size < ids.length) {
            console.warn("[rates " + year + "] " + (ids.length - m.size) + " rows had empty or duplicate keys");
        }
        return m;
    }

    /* ---------- parcel fields ---------- */
    function resolveFields(layer){
        const info = { ok:false, fields:{}, outFields:[] };
        if (layer.loadStatus !== "loaded") {
            console.error('Parcel layer "' + layer.title + '" failed to load; it will be skipped.');
            return info;
        }
        const missing = [];
        for (const [key, name] of Object.entries(PARCEL_FIELDS)) {
            const f = layer.getField(name);
            if (f) info.fields[key] = { name:f.name, domain:(f.domain && f.domain.type === "coded-value") ? f.domain : null };
            else if (key !== "area") missing.push(name);
        }
        if (!info.fields.area) {
            console.warn('"' + layer.title + '": no "' + PARCEL_FIELDS.area + '" field; area will be calculated from the shape.');
        }
        if (missing.length) {
            console.error('"' + layer.title + '" is missing fields: ' + missing.join(", ") +
                '. Available fields:', layer.fields.map(f => f.name));
            return info;
        }
        info.outFields = Object.values(info.fields).map(f => f.name);
        info.ok = true;
        return info;
    }

    function parcelKeys(a, info){
        const labelParts = [], rawParts = [];
        for (const part of KEY_PARTS) {
            const f = info.fields[part];
            const raw = a[f.name];
            let label = raw, rawVal = raw;
            if (f.domain && raw != null) {
                const name = f.domain.getName(raw);
                if (name != null) label = name;
            }
            if (part === "province") {
                const fixL = PROV_FIX.get(normText(label)), fixR = PROV_FIX.get(normText(raw));
                if (fixL != null) label = fixL;
                if (fixR != null) rawVal = fixR;
            }
            labelParts.push(label);
            rawParts.push(rawVal);
        }
        const k1 = normKey(labelParts.join("_")), k2 = normKey(rawParts.join("_"));
        return k1 === k2 ? [k1] : [k1, k2];
    }

    function parcelArea(feature, info){
        if (info.fields.area) {
            const v = toNum(feature.attributes[info.fields.area.name]);
            if (v != null && v > 0) return v * AREA_TO_SQM;
        }
        const g = feature.geometry;
        if (!g || g.type !== "polygon") return null;
        try {
            const sr = g.spatialReference;
            const a = (sr && (sr.isWGS84 || sr.isWebMercator))
                ? geometryEngine.geodesicArea(g, "square-meters")
                : geometryEngine.planarArea(g, "square-meters");
            return Number.isFinite(a) && a !== 0 ? Math.abs(a) : null;
        } catch (err) { return null; }
    }

    function labelPoint(g){
        if (!g) return null;
        if (g.type === "point") return g;
        return g.centroid || (g.extent && g.extent.center) || null;
    }

    function textSymbol(text){
        return {
            type:"text", text, color:"#0f172a", haloColor:"#ffffff", haloSize:1.4,
            font:{ family:"sans-serif", size:9, weight:"bold" }, horizontalAlignment:"center"
        };
    }

    async function queryParcels(p, extent){
        const q = { geometry:extent, spatialRelationship:"intersects", returnGeometry:true, outFields:p.info.outFields };
        try {
            return (await p.lv.queryFeatures(q)).features;
        } catch (err) {
            console.warn('Layer view query failed on "' + p.layer.title + '", falling back to the server:', err);
            return (await p.layer.queryFeatures({ ...q, outSpatialReference:view.spatialReference })).features;
        }
    }

    /* ---------- draw labels (one or both years) ---------- */
    const clearLabels = () => YEAR_LIST.forEach(y => labelLayers[y].removeAll());

    function scheduleDraw(){
        clearTimeout(drawTimer);
        drawTimer = setTimeout(drawLabels, 150);
    }

    async function drawLabels(){
        if (!view || !view.stationary) return;
        const id = ++drawSeq;
        const years = shownYears();
        if (years.some(y => !ratesLoaded[y])) return;   // selectMode() redraws when rates arrive

        if (view.scale > SCALE_LIMIT) { clearLabels(); setHint("Zoom in to see parcel prices"); return; }

        const active = parcels.filter(p => p.info.ok && p.lv && !p.lv.suspended);
        if (!active.length) {
            clearLabels();
            setHint(parcels.some(p => p.info.ok && !p.lv) ? "Loading parcels…" : "No parcel layer visible here");
            return;
        }
        if (active.some(p => p.lv.updating)) { setHint("Loading parcels…"); return; }

        const extent = view.extent.clone();
        let failed = 0;
        const results = await Promise.all(active.map(p =>
            queryParcels(p, extent).catch(err => {
                failed++;
                console.error('Parcel query failed on "' + p.layer.title + '":', err);
                return [];
            })
        ));
        if (id !== drawSeq) return;

        const stats = {};
        years.forEach(y => stats[y] = { graphics:[], matched:0, noArea:0, unmatched:[] });
        let total = 0;

        results.forEach((feats, i) => {
            const p = active[i];
            for (const f of feats) {
                total++;
                const keys = parcelKeys(f.attributes, p.info);
                let area, pt;   // computed lazily, once per parcel
                for (const y of years) {
                    const s = stats[y], rates = ratesLoaded[y];
                    let r = null;
                    for (const k of keys) { r = rates.get(k); if (r) break; }
                    if (!r || r.mean == null) {
                        if (s.unmatched.length < 8) s.unmatched.push({ layer:p.layer.title, triedKeys:keys, hasVillageRow:!!r });
                        continue;
                    }
                    if (area === undefined) area = parcelArea(f, p.info);
                    if (!area) { s.noArea++; continue; }
                    s.matched++;
                    if (s.graphics.length < MAX_LABELS) {
                        if (pt === undefined) pt = labelPoint(f.geometry);
                        if (pt) s.graphics.push(new Graphic({ geometry:pt, symbol:textSymbol(money(r.mean * area)) }));
                    }
                }
            }
        });

        clearLabels();
        years.forEach(y => labelLayers[y].addMany(stats[y].graphics));

        // status text
        let msg, warn = false;
        if (total === 0) {
            msg = "No parcels in view";
        } else if (years.length === 1) {
            const y = years[0], s = stats[y];
            if (!s.matched) {
                msg = total + " parcels in view, none matched " + y + " rates (see console)";
                warn = true; logNoMatch(y, s.unmatched, ratesLoaded[y]);
            } else {
                msg = s.graphics.length + " parcels priced (" + y + ")";
                if (s.matched > s.graphics.length) msg += " · showing " + s.graphics.length + " of " + s.matched;
                const un = total - s.matched - s.noArea;
                if (un > 0) msg += " · " + un + " unmatched";
                if (s.noArea) msg += " · " + s.noArea + " without area";
            }
        } else {
            msg = "Comparing " + years.map(y => y + ": " + stats[y].matched + " priced").join(" · ");
            years.forEach(y => {
                if (!stats[y].matched) { warn = true; logNoMatch(y, stats[y].unmatched, ratesLoaded[y]); }
            });
        }
        if (failed) { msg = failed + " layer(s) failed · " + msg; warn = true; }
        setHint(msg, warn);
    }

    function logNoMatch(year, unmatched, rates){
        if (noMatchLogged.has(year)) return;
        noMatchLogged.add(year);
        console.groupCollapsed("[match " + year + "] No parcels matched. Compare these keys:");
        console.log("Keys built from parcels:", unmatched);
        console.log("Sample village keys:", Array.from(rates.keys()).slice(0, 8));
        console.log("Total village keys cached:", rates.size);
        console.groupEnd();
    }

    /* ---------- layer visibility + swipe ---------- */
    function applyVisibility(){
        const shown = shownYears();
        YEAR_LIST.forEach(y => {
            const on = shown.includes(y);
            const vl = villageLayer(y);
            if (vl) vl.visible = on;
            labelLayers[y].visible = on;
        });
    }

    function placeTags(pos){
        $("tagLeft").style.right = "calc(" + (100 - pos) + "% + 14px)";
        $("tagRight").style.left = "calc(" + pos + "% + 14px)";
    }

    function setSwipe(on){
        if (!view) return;
        if (on && !swipe) {
            const [left, right] = YEAR_LIST;
            const vLeft = villageLayer(left), vRight = villageLayer(right);
            [vLeft, vRight].forEach(vl => {
                if (vl && vl.parent && vl.parent.type === "group" && !vl.parent.visible) {
                    console.warn('"' + vl.title + '" is inside a hidden group; turning the group on for the swipe.');
                    vl.parent.visible = true;
                }
            });
            swipe = new Swipe({
                view, position:50, direction:"horizontal",
                leadingLayers:[vLeft, labelLayers[left]].filter(Boolean),
                trailingLayers:[vRight, labelLayers[right]].filter(Boolean)
            });
            view.ui.add(swipe);
            $("tagLeft").textContent = "◀ " + left;
            $("tagRight").textContent = right + " ▶";
            $("tagLeft").classList.add("show");
            $("tagRight").classList.add("show");
            swipeWatch = reactiveUtils.watch(() => swipe.position, placeTags, { initial:true });
        } else if (!on && swipe) {
            if (swipeWatch) { swipeWatch.remove(); swipeWatch = null; }
            view.ui.remove(swipe);
            swipe.destroy();
            swipe = null;
            $("tagLeft").classList.remove("show");
            $("tagRight").classList.remove("show");
        }
    }

    /* ---------- mode toggle: 2021 / 2024 / Compare ---------- */
    function setButtons(current, disabled){
        document.querySelectorAll("#toggle button").forEach(b => {
            b.disabled = disabled;
            b.classList.toggle("active", b.dataset.mode === current);
        });
    }

    async function selectMode(next){
        mode = next;
        drawSeq++;                        // cancel any draw in progress
        clearLabels();
        setButtons(next, true);
        setSwipe(next === "compare");
        applyVisibility();

        const years = shownYears();
        if (years.some(y => !ratesLoaded[y])) setHint("Loading " + years.join(" and ") + " rates…");
        let ok = true;
        try {
            await Promise.all(years.map(getRates));
        } catch (err) {
            ok = false;
            console.error("Couldn't load rates:", err);
            setHint("Couldn't load rates: " + err.message, true);
        } finally {
            setButtons(mode, false);
        }
        if (mode !== next || !ok) return;  // switched again while loading, or failed
        drawLabels();
    }

    $("toggle").addEventListener("click", e => {
        const btn = e.target.closest("button");
        if (btn && !btn.disabled && btn.dataset.mode !== mode) selectMode(btn.dataset.mode);
    });

    /* ---------- widgets ---------- */
    function addSearch(){
        const sources = parcels.map(p => {
            const f = p.layer.loadStatus === "loaded" ? p.layer.getField(UPI_FIELD) : null;
            if (!f) {
                console.warn('"' + p.layer.title + '" has no "' + UPI_FIELD + '" field; not searchable.');
                return null;
            }
            return {
                layer:p.layer, searchFields:[f.name], displayField:f.name,
                exactMatch:false, outFields:[f.name], name:p.layer.title,
                placeholder:"e.g. 1/03/02/03/3918", zoomScale:1200
            };
        }).filter(Boolean);
        if (!sources.length) return;
        view.ui.add(new Search({
            view, sources, includeDefaultSources:false, locationEnabled:false, allPlaceholder:"Search UPI"
        }), "top-right");
    }

    function addLegend(){
        const panel = document.createElement("div");
        panel.className = "legend-panel";
        panel.innerHTML =
            '<div class="legend-note"><b>Price labels</b>' +
            'Estimated plot value in ' + escapeHtml(CURRENCY) + ': the village average rate × plot size. ' +
            'K = thousand, M = million. Labels appear when you zoom in.</div>' +
            '<div class="legend-host"></div>';
        new Legend({ view, container:panel.querySelector(".legend-host"), respectLayerVisibility:true });
        view.ui.add(new Expand({
            view, content:panel, expandIcon:"legend", expandTooltip:"Legend",
            expanded:window.innerWidth > 800
        }), "bottom-left");
    }

    /* ---------- boot ---------- */
    async function boot(){
        await webmap.load();

        const parcelLayers = webmap.allLayers
            .filter(l => l.type === "feature" && PARCEL_TITLE_RX.test(l.title || ""))
            .toArray();

        setOverlay("Reading layer settings…");
        const village = YEAR_LIST.map(villageLayer).filter(Boolean);
        await Promise.all([...parcelLayers, ...village].map(l =>
            l.load().catch(err => console.error('Layer "' + l.title + '" failed to load:', err))
        ));

        parcels = parcelLayers.map(layer => ({ layer, lv:null, info:resolveFields(layer) }));
        for (const p of parcels) {
            if (!p.info.ok) continue;
            const cur = p.layer.outFields || [];
            if (!cur.includes("*")) p.layer.outFields = [...new Set([...cur, ...p.info.outFields])];
        }
        applyVisibility();

        view = new MapView({ container:"viewDiv", map:webmap });
        await view.when();
        $("overlay").remove();

        webmap.addMany(YEAR_LIST.map(y => labelLayers[y]));   // labels on top
        view.ui.add(new Home({ view }), "top-left");
        addSearch();
        addLegend();

        for (const p of parcels) {
            if (!p.info.ok) continue;
            view.whenLayerView(p.layer).then(lv => {
                p.lv = lv;
                reactiveUtils.when(() => !lv.updating, scheduleDraw);
                reactiveUtils.watch(() => lv.suspended, scheduleDraw);
                scheduleDraw();
            }).catch(err => console.error('No layer view for "' + p.layer.title + '":', err));
        }
        reactiveUtils.when(() => view.stationary, scheduleDraw);

        window.parcelDebug = { view, webmap, parcels, ratesLoaded, getRates, normKey, parcelKeys, selectMode };

        if (!parcels.length) {
            setHint('No layers ending in "Parcels" found — check titles', true);
            console.error("Layer titles in this map:", webmap.allLayers.map(l => l.title).toArray());
        } else if (!parcels.some(p => p.info.ok)) {
            setHint("Parcel layers are missing key fields (see console)", true);
        }

        await selectMode(mode);
        // Prefetch the remaining years so switching and comparing are instant.
        YEAR_LIST.forEach(y => getRates(y).catch(() => {}));
    }

    function showError(err){
        console.error(err);
        const o = $("overlay");
        const detail = err && err.message ? '<br><code>' + escapeHtml(err.message) + '</code>' : "";
        if (o) {
            o.innerHTML = '<div class="err"><b>Couldn\u2019t load the web map.</b><br>' +
                'Check the WEBMAP_ID, that the map and its layers are shared to you, ' +
                'and that this page\u2019s address is allowed on the portal (CORS).' + detail + '</div>';
        } else {
            setHint("Error: " + (err && err.message ? err.message : "see console"), true);
        }
    }

    boot().catch(showError);
});
