/* GRIDLOCK TOWN - interactive town traffic monitor. Pure C99 + raylib (GLSL shaders are plain strings loaded by raylib).
 * A town with a river, two bridges, high street, ring road, winding streets, zones, landmarks and a level crossing.
 * Cars make purposeful trips (home/work/school/shops); signals can be switched off and traffic visibly diverts.
 *
 * Keys: P pause | 1/2/4 speed | C crash | S stadium | R rain | W roadworks | M market day | X clear incidents
 *       E ambulances on/off | T all signals on/off | L signals at hovered junction | O fog | V 2D/3D | Q 3D quality
 *       3D: drag orbit, shift+drag / arrows pan, scroll zoom, Tab camera preset, F chase cam, 0 reset
 * Mouse: click a building for its trips, click a road to close/open it, ctrl+click roadworks, shift+click crash. */
#include "raylib.h"
#include "raymath.h"
#include "rlgl.h"
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define SW 1280
#define SH 800
#define NNODE 67
#define NN 72
#define NE 200
#define NCAR 420
#define NBLD 230
#define NFEED 5
#define NDROP 90
#define NTREE 260
#define NLAMP 120
#define NPED 60
#define NSPL 60
#define PXK 0.3f      /* pixels per (km/h * second) */
#define CLOCKX 40.0f  /* city clock seconds per sim second */
#define OX 68.0f      /* town origin on screen */
#define OY 264.0f
#define V_RES 35.0f
#define V_LOC 50.0f
#define V_HIGH 70.0f
#define V_RING 80.0f
#define V_BR 60.0f

#define C_BG     (Color){10,12,22,255}
#define C_CARD   (Color){19,23,40,255}
#define C_BORDER (Color){35,41,66,255}
#define C_TEXT   (Color){236,239,252,255}
#define C_MUTED  (Color){128,138,170,255}
#define C_CYAN   (Color){56,224,255,255}
#define C_VIOLET (Color){139,92,246,255}
#define C_PINK   (Color){255,87,170,255}
#define C_GREEN  (Color){52,230,160,255}
#define C_AMBER  (Color){255,190,70,255}
#define C_RED    (Color){255,84,104,255}

enum { AL, AC, AR };
enum { BT_HOME, BT_SHOP, BT_OFFICE, BT_SCHOOL, BT_IND, BT_STAD, BT_HOSP, BT_MARKET, BT_MILL, BT_FOUNT, BT_STATION };
typedef struct { float x, y, cycle, off, q; int deg, maxcls, sig, on, lc; } Node;
typedef struct { int a, b, horiz, cls, bridge, closed, cnt, resp; float len, limit, crash, ratio, ux, uy, works, t0, crowd; const char *nm; } Edge;
typedef struct { int on, edge, dst, type, bd, purpose; float pos, v, br, div; } Car;
typedef struct { char t[72]; float clk; Color c; } Feed;
typedef struct { float x, y, w, d, h, fx, fy; int type, acc, gen, att, pg[7], col; } Bld;
typedef struct { int e, dir; float t, wait, spd; Color c; } Ped;
typedef struct { float x0, y0, x1, y1, gx, gy; int type; } Zone;
typedef struct { int from, to, purpose; } Trip;
typedef struct { Color c; char t[40], d[40]; float frac; } Ev;
#define NAMB 3
#define NHOSP 2
typedef struct { int st, edge, dst, hosp, call, node; float pos, onScene; } Amb; /* st: 0 idle, 1 to scene, 2 on scene, 3 to hospital */

static const Rectangle R_MAP = {28, 204, 780, 566}, R_CHART = {828, 204, 424, 190};
static const Rectangle R_HOT = {828, 410, 424, 190}, R_FEED = {828, 616, 424, 154};
static const char *KPI_N[5] = {"Vehicles", "Avg. speed", "Congestion", "Signals", "CO2 today"};
static const char *TOASTS[4] = {"Chain reaction on the road!", "Rush-hour fender bender", "Wet roads, bad timing", "A bumpy moment on the road"};
static const char *TYPE_N[11] = {"House", "Shop", "Office block", "School", "Industrial unit", "Stadium", "Hospital", "Market stalls", "Windmill", "Fountain", "Railway station"};

/* ---- town data (local coordinates, origin added at build time) ---- */
static const float NPT[NNODE][2] = {
  {40,40},{190,18},{380,12},{560,18},{690,45},{705,200},{690,350},{665,445},{535,455},{440,440},{330,440},{190,458},{55,448},{25,310},{22,170},
  {110,196},{190,208},{235,212},{300,215},{335,215},{430,215},{490,212},{545,215},{600,215},{650,208},
  {575,70},{590,135},{655,95},{655,150},{470,92},{482,150},{465,45},{465,14},{525,85},{615,80},
  {495,270},{500,330},{505,390},{645,265},{640,330},{630,400},{565,278},{570,405},
  {95,150},{125,105},{90,65},{200,160},{170,110},{205,65},{145,160},{150,50},{260,90},{305,120},{295,170},
  {100,250},{130,300},{95,350},{110,400},{200,260},{170,310},{190,360},{160,410},{150,262},{140,352},
  {290,270},{300,330},{310,390}};
static const int EDG[][4] = { /* a, b, class (0 residential, 1 local, 2 high street, 3 ring), bridge */
  {0,1,3,0},{1,2,3,0},{2,32,3,0},{32,3,3,0},{3,4,3,0},{4,5,3,0},{5,6,3,0},{6,7,3,0},{7,8,3,0},{8,9,3,0},{9,10,3,1},{10,11,3,0},{11,12,3,0},{12,13,3,0},{13,14,3,0},{14,0,3,0},
  {14,15,2,0},{15,16,2,0},{16,17,2,0},{17,18,2,0},{18,19,2,0},{19,20,2,1},{20,21,2,0},{21,22,2,0},{22,23,2,0},{23,24,2,0},{24,5,2,0},
  {3,25,1,0},{25,26,1,0},{26,23,1,0},{4,27,1,0},{27,28,1,0},{28,24,1,0},{32,31,1,0},{31,29,1,0},{29,30,1,0},{30,21,1,0},{29,33,1,0},{33,25,1,0},{25,34,1,0},{34,27,1,0},
  {21,35,1,0},{35,36,1,0},{36,37,1,0},{37,8,1,0},{24,38,1,0},{38,39,1,0},{39,40,1,0},{40,7,1,0},{35,41,1,0},{41,38,1,0},{37,42,1,0},{42,40,1,0},{39,6,1,0},
  {15,43,0,0},{43,44,0,0},{44,45,0,0},{45,0,0,0},{16,46,0,0},{46,47,0,0},{47,48,0,0},{48,1,0,0},{44,47,0,0},{43,49,0,0},{49,46,0,0},{45,50,0,0},{50,48,0,0},
  {48,51,1,0},{51,52,1,0},{52,53,1,0},{53,18,1,0},
  {15,54,0,0},{54,55,0,0},{55,56,0,0},{56,57,0,0},{57,12,0,0},{16,58,0,0},{58,59,0,0},{59,60,0,0},{60,61,0,0},{61,11,0,0},{54,62,0,0},{62,58,0,0},{55,59,0,0},{56,63,0,0},{63,60,0,0},{57,61,0,0},
  {18,64,1,0},{64,65,1,0},{65,66,1,0},{66,10,1,0}};
static const float RV[8][2] = {{380,70},{380,92},{388,150},{378,215},{372,260},{392,360},{384,440},{380,495}};
static const Zone ZN[6] = {{45,30,300,200,21,19,BT_HOME},{35,225,225,440,21,19,BT_HOME},{250,160,332,264,32,32,BT_SHOP},
  {440,160,700,264,32,32,BT_SHOP},{445,30,690,185,30,26,BT_OFFICE},{440,250,640,440,38,32,BT_IND}};
static const Trip TR[10] = {{BT_HOME,BT_OFFICE,0},{BT_OFFICE,BT_HOME,6},{BT_HOME,BT_IND,1},{BT_IND,BT_HOME,6},{BT_HOME,BT_SCHOOL,2},
  {BT_SCHOOL,BT_HOME,6},{BT_HOME,BT_SHOP,3},{BT_SHOP,BT_HOME,6},{BT_HOME,BT_STAD,4},{BT_HOME,BT_MARKET,5}};
static const int HN_[NHOSP] = {55, 28}; /* hospital junctions */

/* ---- state ---- */
static Font fR, fB;
static Node N[NN];
static Edge E[NE];
static Car cars[NCAR];
static Bld bld[NBLD];
static Ped ped[NPED];
static Feed feed[NFEED];
static Vector2 drops[NDROP];
static Vector3 trees[NTREE]; /* x, z (screen coords), size */
static Vector2 lamps[NLAMP];
static Amb amb[NAMB];
static int nE, nBld, nTree, nLamp, nPed, eid[NN][NN], nxt[NN][NN], nxtOld[NN][NN];
static int paused, speedIdx, rain, trips, lastDay, emgOn = 1, calls, respN, fogMan, routeCause, divSig, selB = -1;
static int view3d, followCar = -1, followAmb = -1, drag3d, camPreset, quality = 1, haveBase, lightsOn, lightsTot, barrierDown, trainDir = 1;
static float simT, clockS = 6.5f * 3600, spawnAcc, stadiumT, marketT, refT, introT, toastT, fogL, trainY, barPos, sinceChange;
static float rerouteT; /* timer for periodic congestion-aware rerouting */
static int routeQuiet; /* 1 during routine reroutes: no "diverted" highlights */
static float purD[7], kpiT[5], kpiD[5], kpiRef[5], delayRate, co2Rate, delayH, co2T, respSum, pathT[NN][NN];
static float emaDelay, emaSpeed, emaQueue, emaThr, baseDelay, baseSpeed, baseQueue, baseThr;
static const char *toastMsg = "";
static struct { int on; char a[64], b[64]; Vector2 p; Color c; } tip;
static float camYaw = .35f, camPitch = .75f, camDist = 75, userDist = 75, followDist = 16, cx3, cy3;
static Vector3 camT;
static RenderTexture2D rt3;

static float rnd(void) { return GetRandomValue(0, 10000) / 10000.0f; }

static float Appr(float c, float t, float r, float dt) { return c + (t - c) * fminf(1.0f, r * dt); }

static float G(float h, float m, float s) { float d = h - m; return expf(-d * d / (2 * s * s)); }

static Color Mix(Color a, Color b, float t) {
  t = Clamp(t, 0, 1);
  return (Color){(unsigned char)(a.r + (b.r - a.r) * t), (unsigned char)(a.g + (b.g - a.g) * t),
                 (unsigned char)(a.b + (b.b - a.b) * t), (unsigned char)(a.a + (b.a - a.a) * t)};
}

static void Txt(const char *s, float x, float y, float sz, Color c, int bold, int al) {
  Font f = bold ? fB : fR; float sp = sz * 0.01f; Vector2 m = MeasureTextEx(f, s, sz, sp);
  if (al == AC) x -= m.x / 2; else if (al == AR) x -= m.x;
  DrawTextEx(f, s, (Vector2){floorf(x), floorf(y)}, sz, sp, c);
}

static float TW(const char *s, float sz, int bold) { return MeasureTextEx(bold ? fB : fR, s, sz, sz * 0.01f).x; }

static void RR(Rectangle r, float rad, Color c) {
  float k = rad / (fminf(r.width, r.height) / 2); if (k > 1) k = 1;
  DrawRectangleRounded(r, k, 10, c);
}

static int Hover(Rectangle r) { return CheckCollisionPointRec(GetMousePosition(), r); }

static void Card(Rectangle r, Color border) {
  RR((Rectangle){r.x - 1, r.y - 1, r.width + 2, r.height + 2}, 17, border);
  RR(r, 16, C_CARD);
}

static void SetTip(const char *a, const char *b, Vector2 p, Color c) {
  tip.on = 1; snprintf(tip.a, 64, "%s", a); snprintf(tip.b, 64, "%s", b); tip.p = p; tip.c = c;
}

static void Toast(const char *m) { toastMsg = m; toastT = 3.0f; }

static void AddFeed(const char *t, Color c) {
  memmove(feed + 1, feed, (NFEED - 1) * sizeof(Feed));
  snprintf(feed[0].t, 72, "%s", t); feed[0].clk = clockS; feed[0].c = c;
}

static float SegD(Vector2 p, Vector2 a, Vector2 b) {
  Vector2 ab = Vector2Subtract(b, a);
  float t = Clamp(Vector2DotProduct(Vector2Subtract(p, a), ab) / Vector2DotProduct(ab, ab), 0, 1);
  return Vector2Distance(p, Vector2Add(a, Vector2Scale(ab, t)));
}

static Color SigCol(int s) { return s == 1 ? C_GREEN : s == 2 ? C_AMBER : C_RED; }

static Vector2 NP(int n) { return (Vector2){N[n].x, N[n].y}; }


static float DayF(void) { return Clamp(sinf((fmodf(clockS / 3600, 24) - 6) / 12 * PI), 0, 1); }
static void NName(int n, char *o) { snprintf(o, 8, "J%02u", (unsigned)(n + 1) % 100u); }
static float RW(int cls) { return cls == 3 ? 18.0f : cls == 2 ? 17.0f : cls == 1 ? 12.0f : 10.0f; }
static float RiverD(float x, float y) {
  float m = 1e9f;
  for (int i = 0; i < 7; i++) {
    float d = SegD((Vector2){x, y}, (Vector2){OX + RV[i][0], OY + RV[i][1]}, (Vector2){OX + RV[i + 1][0], OY + RV[i + 1][1]});
    if (d < m) m = d;
  }
  return m;
}

/* ---------- network, routing, signals ---------- */
static void AddRoad(int a, int b, int cls, int br) {
  float len = Vector2Distance(NP(a), NP(b)), ux = (N[b].x - N[a].x) / len, uy = (N[b].y - N[a].y) / len;
  float lim = br ? V_BR : cls == 3 ? V_RING : cls == 2 ? V_HIGH : cls == 1 ? V_LOC : V_RES;
  const char *nm = br ? (cls == 3 ? "Ring Road Bridge" : "High Street Bridge") : cls == 3 ? "Ring Road" : cls == 2 ? "High Street" : cls == 1 ? "Local road" : "Residential street";
  E[nE] = (Edge){.a = a, .b = b, .horiz = fabsf(ux) > fabsf(uy), .cls = cls, .bridge = br, .len = len, .limit = lim, .ratio = 1, .ux = ux, .uy = uy, .nm = nm};
  E[nE + 1] = (Edge){.a = b, .b = a, .horiz = fabsf(ux) > fabsf(uy), .cls = cls, .bridge = br, .len = len, .limit = lim, .ratio = 1, .ux = -ux, .uy = -uy, .nm = nm};
  eid[a][b] = nE; eid[b][a] = nE + 1; nE += 2;
  N[a].deg++; N[b].deg++; if (cls > N[a].maxcls) N[a].maxcls = cls; if (cls > N[b].maxcls) N[b].maxcls = cls;
}
static float NodePen(int n) { return (N[n].sig && !N[n].on ? 2.5f : 0) + (N[n].lc ? .8f : 0); }
static void Route(void) { /* Floyd-Warshall on travel time; closures, crashes, roadworks and unsignalised junctions add cost */
  static float d[NN][NN];
  memcpy(nxtOld, nxt, sizeof nxt);
  for (int i = 0; i < NN; i++) for (int j = 0; j < NN; j++) { d[i][j] = i == j ? 0 : 1e9f; nxt[i][j] = -1; }
  for (int e = 0; e < nE; e++) {
    float w = E[e].len / E[e].limit + NodePen(E[e].b);
    if (E[e].closed) w = 1e6f; else if (E[e].crash > 0) w *= 8; else if (E[e].works > 0) w *= 3; else if (E[e].crowd > 0) w *= 1.4f;
    if (!E[e].closed) w *= 1 + 1.5f * fminf(1, E[e].cnt * 11.0f / E[e].len); /* congestion: how full the street is (short streets fill fast) */
    if (w < d[E[e].a][E[e].b]) { d[E[e].a][E[e].b] = w; nxt[E[e].a][E[e].b] = E[e].b; }
  }
  for (int k = 0; k < NN; k++) for (int i = 0; i < NN; i++) for (int j = 0; j < NN; j++)
    if (d[i][k] + d[k][j] < d[i][j]) { d[i][j] = d[i][k] + d[k][j]; nxt[i][j] = nxt[i][k]; }
  memcpy(pathT, d, sizeof pathT);
  for (int i = 0; i < NCAR; i++) if (cars[i].on) { /* highlight cars whose next turn changed: they are being diverted */
    Car *c = &cars[i]; int oa = E[c->edge].b, na = oa, diff = 0;
    for (int s = 0; s < 4 && oa != c->dst && na != c->dst && !diff; s++) { /* compare the next few turns of the old and new routes */
      int o2 = nxtOld[oa][c->dst], n2 = nxt[na][c->dst];
      if (o2 < 0 || n2 < 0) break;
      if (o2 != n2) diff = 1;
      oa = o2; na = n2;
    }
    if (diff && !routeQuiet) { c->div = 40; if (routeCause == 1) divSig++; }
  }
}
static int Sig(int n, int horiz) { /* 0 red, 1 green, 2 amber, 4 no signal (give-way) */
  float cy, t, half, rem; int hp;
  if (N[n].lc) return barrierDown ? 0 : 1;
  if (!N[n].sig || !N[n].on) return 4;
  cy = N[n].cycle; t = fmodf(simT + N[n].off, cy); half = cy * .5f; hp = t < half; rem = hp ? half - t : cy - t;
  if (horiz != hp) return 0;
  return rem < 1.2f ? 2 : 1;
}
static int Conflict(Edge *e, int ne, Edge *oe, int one) { /* do two movements through the same junction cross paths? ne/one = exit edges (-1: trip ends here) */
  if (ne < 0 || one < 0) return 0;
  if (one == ne) return 1; /* merging into the same street */
  if (e->ux * oe->ux + e->uy * oe->uy < -.8f) /* oncoming: straight and right turns pass each other, only a left turn crosses */
    return e->ux * E[ne].uy - e->uy * E[ne].ux < -.35f;
  return 1; /* side-on approaches cross */
}
static int Yield(int i, Edge *e, int n) { /* side streets give way to main roads; equal roads: nearest car first; only to cars whose path crosses ours */
  Car *c = &cars[i]; float rem = e->len - c->pos; int nn, ne;
  if (rem > 40) return 0;
  nn = c->dst == n ? -1 : nxt[n][c->dst]; ne = nn >= 0 ? eid[n][nn] : -1;
  for (int j = 0; j < NCAR; j++) {
    Car *o = &cars[j]; Edge *oe; float orem; int on, one;
    if (!o->on || j == i || o->edge == c->edge) continue;
    oe = &E[o->edge]; if (oe->b != n) continue;
    orem = oe->len - o->pos; if (orem > 45) continue;
    on = o->dst == n ? -1 : nxt[n][o->dst]; one = on >= 0 ? eid[n][on] : -1;
    if (!Conflict(e, ne, oe, one)) continue;
    if (oe->cls > e->cls || (oe->cls == e->cls && (orem + 5 < rem || (fabsf(orem - rem) <= 5 && j < i)))) return 1;
  }
  return 0;
}

/* ---------- building the town ---------- */
static int FreeSpot(float x, float y, float r, float rb) {
  if (x < OX + 8 || x > OX + 712 || y < OY + 8 || y > OY + 484) return 0;
  for (int e = 0; e < nE; e += 2) if (SegD((Vector2){x, y}, NP(E[e].a), NP(E[e].b)) < RW(E[e].cls) / 2 + r + 2) return 0;
  if (RiverD(x, y) < 24 + r) return 0;
  if (fabsf(x - (OX + 235)) < 16 + r && y > OY + 100 && y < OY + 405) return 0;
  if (x > OX + 498 && x < OX + 595 && y > OY + 145 && y < OY + 210) return 0;
  for (int b = 0; b < nBld; b++) if (Vector2Distance((Vector2){x, y}, (Vector2){bld[b].x, bld[b].y}) < rb + .5f * hypotf(bld[b].w, bld[b].d) * .8f) return 0;
  return 1;
}
static void AddBld(float x, float y, float w, float d, float h, int type, int acc) {
  Bld *b; float md = 1e9f; int be = -1;
  if (nBld >= NBLD) return;
  b = &bld[nBld++]; memset(b, 0, sizeof *b);
  b->x = x; b->y = y; b->w = w; b->d = d; b->h = h; b->type = type; b->col = GetRandomValue(0, 4); b->fx = 1;
  for (int e = 0; e < nE; e += 2) { float dd = SegD((Vector2){x, y}, NP(E[e].a), NP(E[e].b)); if (dd < md) { md = dd; be = e; } }
  if (be >= 0 && type != BT_STAD && type != BT_MILL && type != BT_FOUNT) { b->fx = E[be].ux; b->fy = E[be].uy; }
  if (acc >= 0) b->acc = acc;
  else { float bd = 1e9f; for (int n = 0; n < NNODE; n++) { float dd = Vector2Distance((Vector2){x, y}, NP(n)); if (dd < bd) { bd = dd; b->acc = n; } } }
}
static void BuildTown(void) {
  for (int i = 0; i < NN; i++) for (int j = 0; j < NN; j++) eid[i][j] = -1;
  for (int i = 0; i < NNODE; i++) { N[i].x = OX + NPT[i][0]; N[i].y = OY + NPT[i][1]; N[i].cycle = 24; N[i].off = rnd() * 24; }
  for (int i = 0; i < (int)(sizeof EDG / sizeof EDG[0]); i++) AddRoad(EDG[i][0], EDG[i][1], EDG[i][2], EDG[i][3]);
  for (int i = 0; i < NNODE; i++) { N[i].sig = N[i].deg >= 3 && N[i].maxcls >= 2; N[i].on = N[i].sig; if (N[i].sig) lightsTot++; }
  N[17].lc = 1;
  AddBld(OX + 88, OY + 300, 30, 24, 3.2f, BT_HOSP, HN_[0]); AddBld(OX + 625, OY + 150, 34, 24, 3.2f, BT_HOSP, HN_[1]);
  AddBld(OX + 270, OY + 332, 32, 26, 2.4f, BT_SCHOOL, 65); AddBld(OX + 598, OY + 333, 60, 60, 1.8f, BT_STAD, 39);
  AddBld(OX + 545, OY + 193, 70, 16, 1.0f, BT_MARKET, 22); AddBld(OX + 545, OY + 168, 24, 24, .6f, BT_FOUNT, 22);
  AddBld(OX + 62, OY + 108, 18, 18, 3.8f, BT_MILL, 44); AddBld(OX + 235, OY + 100, 26, 16, 1.2f, BT_STATION, -1); AddBld(OX + 235, OY + 404, 26, 16, 1.2f, BT_STATION, -1);
  for (int z = 0; z < 6; z++) for (float gx = ZN[z].x0 + ZN[z].gx / 2; gx < ZN[z].x1; gx += ZN[z].gx) for (float gy = ZN[z].y0 + ZN[z].gy / 2; gy < ZN[z].y1; gy += ZN[z].gy) {
    int t = ZN[z].type; float w = t == BT_HOME ? 17 + rnd() * 5 : t == BT_SHOP ? 28 : t == BT_OFFICE ? 24 + rnd() * 4 : 34;
    float d = t == BT_HOME ? 14 + rnd() * 4 : t == BT_SHOP ? 22 : t == BT_OFFICE ? 20 + rnd() * 4 : 26;
    float h = t == BT_HOME ? 1.2f + rnd() * .5f : t == BT_SHOP ? 1.7f + rnd() * .5f : t == BT_OFFICE ? 3 + rnd() * 6 : 1.8f + rnd() * .9f;
    float x = OX + gx + (rnd() - .5f) * 4, y = OY + gy + (rnd() - .5f) * 4, r = .5f * fminf(w, d) + 1;
    if (FreeSpot(x, y, r, .5f * hypotf(w, d) * .8f)) AddBld(x, y, w, d, h, t, -1);
  }
  for (int k = 0; k < 700 && nTree < NTREE; k++) { /* trees: park, gardens and verges */
    float x, y; int park = k < 260;
    if (park) { x = OX + 315 + rnd() * 125; y = OY + 28 + rnd() * 108; if (hypotf(x - (OX + 380), y - (OY + 70)) < 34 || RiverD(x, y) < 26) continue; }
    else { x = OX + 30 + rnd() * 660; y = OY + 25 + rnd() * 450; if (rnd() < .5f && (x > OX + 330 && x < OX + 440)) continue; }
    if (FreeSpot(x, y, 5, 4)) { trees[nTree++] = (Vector3){x, y, .7f + rnd() * .7f}; }
  }
  for (int e = 0; e < nE; e += 2) if (E[e].cls >= 1 && !E[e].bridge) {
    int n = (int)(E[e].len / 80); float nx = -E[e].uy, ny = E[e].ux;
    for (int k = 0; k <= n && nLamp < NLAMP; k++) {
      float s = ((k + .5f) / (n + 1)) * E[e].len, side = (k % 2 ? 1 : -1) * (RW(E[e].cls) / 2 + 3.5f);
      lamps[nLamp++] = (Vector2){N[E[e].a].x + E[e].ux * s + nx * side, N[E[e].a].y + E[e].uy * s + ny * side};
    }
  }
  for (int pass = 0; pass < 2; pass++) for (int e = 0; e < nE && nPed < NPED; e++) {
    if (!N[E[e].b].sig || N[E[e].b].deg < 3 || RW(E[e].cls) > 20) continue;
    if (pass == 1 && rnd() < .5f) continue;
    ped[nPed++] = (Ped){e, rnd() < .5f ? 1 : -1, 0, rnd() * 6, 5 + rnd() * 2, (Color){(unsigned char)(80 + rnd() * 160), (unsigned char)(60 + rnd() * 160), (unsigned char)(80 + rnd() * 160), 255}};
    ped[nPed - 1].t = ped[nPed - 1].dir > 0 ? 0 : 1;
  }
  Route();
}

/* ---------- simulation ---------- */
static float TripRate(int k, float h) {
  switch (k) {
    case 0: return 1.1f * G(h, 8, .9f);
    case 1: return 1.0f * G(h, 17.5f, 1.1f);
    case 2: return .45f * G(h, 6.8f, .7f);
    case 3: return .4f * G(h, 15.1f, .8f);
    case 4: return .5f * G(h, 8.4f, .35f);
    case 5: return .5f * G(h, 15.4f, .45f);
    case 6: return .3f * (G(h, 10.5f, 1.6f) + .8f * G(h, 16, 1.8f));
    case 7: return .28f * (G(h, 12, 1.8f) + G(h, 17, 1.8f));
    case 8: { /* stadium crowd: builds, peaks mid-event, tails off */
      float f = 1.0f - stadiumT / 90.0f;       /* 0 at start, 1 at end */
      return stadiumT > 0 ? .55f * sinf(PI * f) + .05f : 0;
    }
    default: return marketT > 0 ? .7f : 0;
  }
}
static void SpawnTrip(int k) {
  int ob = -1, db = -1, cO = 0, cD = 0, slot = -1, o, d, nn, e;
  for (int b = 0; b < nBld; b++) { if (bld[b].type == TR[k].from && rnd() * ++cO < 1) ob = b; if (bld[b].type == TR[k].to && rnd() * ++cD < 1) db = b; }
  if (ob < 0 || db < 0) return;
  o = bld[ob].acc; d = bld[db].acc;
  if (bld[db].type == BT_STAD && rnd() < .5f) d = 40; /* second stadium entrance (south side) */
  if (o == d) return;
  nn = nxt[o][d]; if (nn < 0) return;
  e = eid[o][nn];
  for (int i = 0; i < NCAR; i++) { if (!cars[i].on) { if (slot < 0) slot = i; } else if (cars[i].edge == e && cars[i].pos < 14) return; }
  if (slot < 0) return;
  { float r = rnd(); cars[slot] = (Car){.on = 1, .edge = e, .dst = d, .type = r < .08f ? 2 : r < .24f ? 1 : 0, .bd = db, .purpose = TR[k].purpose, .v = E[e].limit * .6f}; }
  bld[ob].gen++; bld[db].att++; if (bld[ob].type == BT_HOME) bld[ob].pg[TR[k].purpose]++;
}
static int PickCrashEdge(void) { /* bridges and unsignalised junctions are more crash-prone */
  float tot = 0, w[NE], r;
  for (int e = 0; e < nE; e++) {
    w[e] = 0; if (E[e].closed || E[e].crash > 0) continue;
    w[e] = (E[e].cnt + .15f) * (E[e].bridge ? 3.0f : 1.0f) * (N[E[e].b].sig && !N[E[e].b].on ? 1.6f : 1.0f) * (rain ? 1.3f : 1.0f); tot += w[e];
  }
  if (tot <= 0) return -1;
  r = rnd() * tot;
  for (int e = 0; e < nE; e++) { r -= w[e]; if (r <= 0 && w[e] > 0) return e; }
  return -1;
}
static void StartCrash(int e) {
  char a[8], b[8], t[72];
  if (E[e].crash > 0) { E[e].crash = 0; routeCause = 2; Route(); AddFeed("Crash cleared", C_GREEN); Toast("Crash cleared"); return; }
  if (E[e].closed) { Toast("That road is closed"); return; }
  E[e].crash = 70; routeCause = 2; Route();
  NName(E[e].a, a); NName(E[e].b, b); snprintf(t, 72, "Crash on %s > %s", a, b);
  AddFeed(t, C_RED); Toast(E[e].bridge ? "Crash on the bridge! Expect long delays" : TOASTS[GetRandomValue(0, 3)]);
}
static void DoCrash(void) { int c = PickCrashEdge(); if (c >= 0) StartCrash(c); }
static void DoStadium(void) {
  if (stadiumT > 0) { stadiumT = 0; AddFeed("Stadium event ended early", C_GREEN); Toast("Stadium event ended"); return; }
  stadiumT = 90; AddFeed("Stadium event: heavy traffic to the ground", C_VIOLET); Toast("Stadium event - supporters heading to the ground");
}
static void DoMarket(void) {
  if (marketT > 0) { marketT = 0; AddFeed("Market day ended", C_GREEN); Toast("Market day ended"); return; }
  marketT = 90; AddFeed("Market day: crowds in the square", C_AMBER); Toast("Market day! Shoppers flood the high street");
}
static void DoRain(void) {
  rain = !rain; AddFeed(rain ? "Rain started: speeds drop" : "Rain cleared", C_CYAN); Toast(rain ? "Rain rolling in" : "Skies clearing");
}
static void DoFog(void) { fogMan = !fogMan; Toast(fogMan ? "Fog rolling in" : "Fog lifting"); }
static int CrashOn(void) { for (int e = 0; e < nE; e++) if (E[e].crash > 0) return 1; return 0; }

static int WorksOn(void) { for (int e = 0; e < nE; e += 2) if (E[e].works > 0) return 1; return 0; }

static void StartWorks(int e) {
  char a[8], b[8], t[72]; e &= ~1;
  if (E[e].works > 0) { E[e].works = E[e + 1].works = 0; routeCause = 2; Route(); AddFeed("Roadworks removed", C_GREEN); Toast("Roadworks removed"); return; }
  if (E[e].closed) { Toast("Can't place roadworks on a closed road"); return; }
  E[e].works = E[e + 1].works = 120; routeCause = 2; Route();
  NName(E[e].a, a); NName(E[e].b, b); snprintf(t, 72, "Roadworks on %s - %s (slow zone)", a, b);
  AddFeed(t, C_AMBER); Toast("Roadworks started - expect delays");
}
static void DoWorks(void) {
  for (int k = 0; k < 60; k++) { int c = GetRandomValue(0, nE / 2 - 1) * 2; if (!E[c].closed && E[c].works <= 0 && E[c].crash <= 0 && !E[c].bridge) { StartWorks(c); return; } }
}
static void ClearIncidents(void) {
  if (!CrashOn() && !WorksOn()) return;
  for (int e = 0; e < nE; e++) E[e].crash = E[e].works = 0;
  routeCause = 2; Route(); AddFeed("All crashes and roadworks cleared", C_GREEN); Toast("All incidents cleared");
}
static void Dispatch(void) { /* nearest free unit by travel time (all-pairs times from Route) */
  for (int e = 0; e < nE; e++) {
    int best = -1; float bt = 1e8f;
    if (E[e].crash <= 0) { E[e].resp = 0; continue; }
    if (E[e].resp == 0) { /* classify the crash once: 60% serious (needs an ambulance), 40% minor */
      E[e].t0 = clockS;
      if (rnd() < .6f) { E[e].resp = 1; calls++; } else { E[e].resp = 3; E[e].crash = fminf(E[e].crash, 30); }
    }
    if (E[e].resp != 1 || !emgOn) continue;
    for (int k = 0; k < NAMB; k++) if (amb[k].st == 0 && pathT[amb[k].node][E[e].a] < bt) { bt = pathT[amb[k].node][E[e].a]; best = k; }
    if (best < 0) continue;
    { Amb *a = &amb[best]; int nn = a->node == E[e].a ? -1 : nxt[a->node][E[e].a];
      if (nn < 0 && a->node != E[e].a) continue;
      a->call = e; a->dst = E[e].a; E[e].resp = 2; a->pos = 0;
      if (nn < 0) { a->st = 2; a->onScene = 10; E[e].crash = fminf(E[e].crash, 10); respSum += clockS - E[e].t0; respN++; }
      else { a->st = 1; a->edge = eid[a->node][nn]; } }
  }
}

static void AmbStep(float dt) {
  for (int k = 0; k < NAMB; k++) {
    Amb *a = &amb[k];
    if (a->st == 1 && E[a->call].crash <= 0) { /* call cancelled: head for the nearest hospital */
      int n = E[a->edge].b; float bt = 1e8f; a->st = 3;
      for (int h = 0; h < NHOSP; h++) if (pathT[n][HN_[h]] < bt) { bt = pathT[n][HN_[h]]; a->dst = HN_[h]; }
    }
    if (a->st == 1 || a->st == 3) {
      Edge *e = &E[a->edge]; float v = e->limit * (.6f + .65f * e->ratio) * (rain ? .85f : 1); /* weaves through queues */
      a->pos += v * PXK * dt;
      if (a->pos >= e->len) {
        int n = e->b, nn = n == a->dst ? -1 : nxt[n][a->dst];
        if (nn >= 0) { a->edge = eid[n][nn]; a->pos -= e->len; }
        else {
          a->node = n; a->pos = 0;
          if (a->st == 1) { a->st = 2; a->onScene = 10; E[a->call].crash = fminf(E[a->call].crash, 10); respSum += clockS - E[a->call].t0; respN++; }
          else { a->st = 0; for (int h = 0; h < NHOSP; h++) if (HN_[h] == n) a->hosp = h; }
        }
      }
    } else if (a->st == 2) {
      a->onScene -= dt;
      if (a->onScene <= 0) {
        float bt = 1e8f; int nn; a->st = 3;
        for (int h = 0; h < NHOSP; h++) if (pathT[a->node][HN_[h]] < bt) { bt = pathT[a->node][HN_[h]]; a->dst = HN_[h]; }
        nn = a->node == a->dst ? -1 : nxt[a->node][a->dst];
        if (nn >= 0) { a->edge = eid[a->node][nn]; a->pos = 0; } else a->st = 0;
      }
    }
  }
}


/* signals: the baseline captured at each change lets the dashboard show before/after */
static void SnapBase(void) { baseDelay = emaDelay; baseSpeed = emaSpeed; baseQueue = emaQueue; baseThr = emaThr; haveBase = 1; sinceChange = 0; divSig = 0; }
static void ToggleNode(int n) {
  char a[8], t[72];
  if (n < 0 || !N[n].sig) { Toast("No traffic signals at this junction"); return; }
  SnapBase(); N[n].on = !N[n].on; routeCause = 1; Route();
  NName(n, a); snprintf(t, 72, "Signals %s at %s", N[n].on ? "restored" : "switched off", a); AddFeed(t, N[n].on ? C_GREEN : C_AMBER);
  Toast(N[n].on ? "Signals back on - traffic recovering" : "Signals off - junction is now give-way");
}
static void ToggleAll(void) {
  int any = 0;
  for (int n = 0; n < NNODE; n++) if (N[n].sig && N[n].on) any = 1;
  SnapBase(); for (int n = 0; n < NNODE; n++) if (N[n].sig) N[n].on = !any;
  routeCause = 1; Route();
  AddFeed(any ? "All signals switched off" : "All signals restored", any ? C_AMBER : C_GREEN); Toast(any ? "All signals OFF - watch traffic divert" : "All signals back on");
}
static void TrainStep(float dt) {
  float tp = fmodf(simT, 90.0f), y0 = OY + 110, y1 = OY + 395, f; int moving = tp < 18;
  trainDir = ((int)(simT / 90.0f) % 2 == 0) ? 1 : -1;
  f = moving ? tp / 18 : 1;
  trainY = trainDir > 0 ? y0 + (y1 - y0) * f : y1 - (y1 - y0) * f;
  { float s = (trainY - N[17].y) * trainDir; barrierDown = moving && s > -150 && s < 90; }
  barPos = Appr(barPos, (float)barrierDown, 2.5f, dt);
}
static void PedStep(float dt) { /* pedestrians cross only while their road has a red light */
  for (int i = 0; i < nPed; i++) {
    Ped *p = &ped[i]; Edge *e = &E[p->e];
    if (p->wait > 0) { p->wait -= dt; continue; }
    if ((p->t <= .001f && p->dir > 0) || (p->t >= .999f && p->dir < 0)) { if (Sig(e->b, e->horiz) != 0) continue; }
    p->t += p->dir * p->spd / (RW(e->cls) + 4) * dt;
    if (p->t >= 1) { p->t = 1; p->dir = -1; p->wait = 2 + rnd() * 8; }
    if (p->t <= 0) { p->t = 0; p->dir = 1; p->wait = 2 + rnd() * 8; }
  }
}
static void SimStep(float dt) {
  float h, rs[NE] = {0}, qraw[NN] = {0}, sumV = 0, sumDelay = 0, sumG = 0, dtc = dt * CLOCKX, tot = 0, rt[10], sumQ = 0; int rc[NE] = {0}, pc[7] = {0}, cnt = 0, arr = 0;
  simT += dt; clockS += dtc; sinceChange += dt; if (stadiumT > 0) stadiumT -= dt; if (marketT > 0) marketT -= dt;
  { int dn = (int)(clockS / 86400); if (dn != lastDay) { lastDay = dn; delayH = co2T = 0; for (int b = 0; b < nBld; b++) { bld[b].gen = bld[b].att = 0; memset(bld[b].pg, 0, sizeof bld[b].pg); } AddFeed("New day: daily totals reset", C_CYAN); } }
  for (int e = 0; e < nE; e++) if (E[e].crash > 0) {
    E[e].crash -= dt;
    if (E[e].crash <= 0) { E[e].crash = 0; routeCause = 2; Route(); AddFeed("Crash cleared, flow recovering", C_GREEN); }
  }
  for (int e = 0; e < nE; e += 2) if (E[e].works > 0) {
    E[e].works -= dt; E[e + 1].works = E[e].works;
    if (E[e].works <= 0) { E[e].works = E[e + 1].works = 0; routeCause = 2; Route(); AddFeed("Roadworks finished, full speed restored", C_GREEN); }
  }
  for (int e = 0; e < nE; e++) E[e].crowd = (marketT > 0 && E[e].a >= 21 && E[e].a <= 23 && E[e].b >= 21 && E[e].b <= 23) ? 1.0f : 0;
  h = fmodf(clockS / 3600, 24);
  { unsigned dn = (unsigned)((int)(clockS / 86400) * 2654435761u); float want = fogMan ? 1.0f : (((dn >> 7) % 100) < 22 && h > 5 && h < 9.5f) ? 1.0f : 0; fogL = Appr(fogL, want, .4f, dt); }
  TrainStep(dt); PedStep(dt); Dispatch(); AmbStep(dt);
  if (rnd() < dt / 240.0f) DoCrash(); /* ambient crashes, more likely on bridges */
  for (int k = 0; k < 10; k++) { rt[k] = TripRate(k, h); tot += rt[k]; }
  spawnAcc += tot * 0.8f *(rain ? 1.08f : 1) * dt;
  while (spawnAcc >= 1) { float r = rnd() * tot; int k = 9; spawnAcc -= 1; for (int q = 0; q < 10; q++) { r -= rt[q]; if (r <= 0) { k = q; break; } } SpawnTrip(k); }
  for (int i = 0; i < NCAR; i++) {
    Car *c = &cars[i]; Edge *e; int n, nn = -1, ne = -1, atDst, blocked = 0, st = 1;
    float gap = 1e9f, vmax, sl, tg, ratio;
    if (!c->on) continue;
    if (c->div > 0) c->div -= dt;
    e = &E[c->edge]; n = e->b; atDst = (n == c->dst);
    for (int j = 0; j < NCAR; j++)
      if (j != i && cars[j].on && cars[j].edge == c->edge && cars[j].pos > c->pos) { float g = cars[j].pos - c->pos - 7; if (g < gap) gap = g; }
    if (!atDst) {
      nn = nxt[n][c->dst]; if (nn < 0) { c->on = 0; continue; }
      ne = eid[n][nn]; sl = e->len - c->pos;
      st = Sig(n, e->horiz);
      if (st == 0 || st == 2) blocked = 1;
      else if (st == 4 && N[n].deg >= 3 && Yield(i, e, n)) blocked = 1;
      if (sl < 24) for (int j = 0; j < NCAR; j++) if (cars[j].on && cars[j].edge == ne && cars[j].pos < 12) { blocked = 1; break; }
    }
    sl = e->len - c->pos;
    if (blocked && sl - 14 < gap) gap = sl - 14;
    vmax = e->limit * (c->type == 2 ? .8f : c->type == 1 ? .92f : 1) * (rain ? .82f : 1) * (e->crash > 0 ? .12f : 1) * (e->works > 0 ? .4f : 1) * (e->crowd > 0 ? .6f : 1) * (1 - .12f * fogL);
    if (!atDst && st == 4 && N[n].deg >= 3 && sl < 45 && vmax > 25 && N[n].sig) vmax = 25; /* give-way junctions cut capacity */
    tg = fminf(vmax, 2.2f * fmaxf(0, gap - 4));
    c->br = tg < c->v - 2 ? 1.0f : 0;
    c->v += Clamp(tg - c->v, -80 * dt, 40 * dt); if (c->v < 0) c->v = 0;
    c->pos += c->v * PXK * dt;
    if (c->pos >= e->len) {
      if (atDst) { c->on = 0; trips++; arr++; continue; }
      if (!blocked) { c->pos -= e->len; c->edge = ne; e = &E[ne]; } else c->pos = e->len;
    }
    ratio = fminf(1, c->v / e->limit);
    rs[c->edge] += ratio; rc[c->edge]++; cnt++; pc[c->purpose]++;
    sumV += c->v; sumDelay += 1 - ratio; sumG += c->v < 5 ? .8f : .4f + .037f * c->v;
    if (c->v < 6 && e->len - c->pos < 50) qraw[e->b] += 1;
  }
  for (int e = 0; e < nE; e++) { E[e].ratio = Appr(E[e].ratio, rc[e] ? rs[e] / rc[e] : 1, 4, dt); E[e].cnt = rc[e]; }
  rerouteT += dt; if (rerouteT >= 4) { rerouteT = 0; routeQuiet = 1; Route(); routeQuiet = 0; } /* drivers react to congestion every few seconds */
  for (int n = 0; n < NNODE; n++) { N[n].q = Appr(N[n].q, qraw[n], 3, dt); sumQ += N[n].q; }
  for (int p = 0; p < 7; p++) purD[p] = Appr(purD[p], (float)pc[p], 1.5f, dt);
  delayH += sumDelay * dtc / 3600; co2T += sumG * dtc / 1e6f; delayRate = sumDelay; co2Rate = sumG * 3.6f;
  lightsOn = 0; for (int n = 0; n < NNODE; n++) if (N[n].sig && N[n].on) lightsOn++;
  kpiT[0] = (float)cnt; kpiT[1] = cnt ? sumV / cnt : 40; kpiT[2] = cnt ? sumDelay / cnt * 100 : 0; kpiT[3] = (float)lightsOn; kpiT[4] = co2T;
  emaDelay = Appr(emaDelay, sumDelay, .05f, dt); emaSpeed = Appr(emaSpeed, kpiT[1], .05f, dt); emaQueue = Appr(emaQueue, sumQ, .05f, dt);
  emaThr = Appr(emaThr, arr / dt, .05f, dt);
  refT += dt; if (refT >= 30) { refT = 0; memcpy(kpiRef, kpiT, sizeof kpiT); }
}

/* ---------- picking, colours ---------- */
static void PickAt(Vector2 p, int *hn, int *he, int *hb) {
  float md = 1e9f; *hn = *he = *hb = -1;
  for (int i = 0; i < NNODE; i++) if (Vector2Distance(p, NP(i)) < 12) { *hn = i; return; }
  for (int b = nBld - 1; b >= 0; b--) {
    Bld *q = &bld[b]; float dx = p.x - q->x, dy = p.y - q->y, u = dx * q->fx + dy * q->fy, v = -dx * q->fy + dy * q->fx;
    if (fabsf(u) <= q->w / 2 + 1 && fabsf(v) <= q->d / 2 + 1) { *hb = b; return; }
  }
  for (int e = 0; e < nE; e += 2) { float d = SegD(p, NP(E[e].a), NP(E[e].b)); if (d < RW(E[e].cls) / 2 + 2 && d < md) { md = d; *he = e; } }
}
static Color BCol(int t) {
  static const Color c[11] = {{196,160,140,255},{224,170,70,255},{110,140,210,255},{120,200,140,255},{130,134,150,255},{160,90,220,255},
                              {235,240,252,255},{240,130,100,255},{210,190,150,255},{80,150,220,255},{150,150,170,255}};
  return c[t];
}
static Color RoadCol(int cls, int br) {
  return br ? (Color){74, 80, 116, 255} : cls == 3 ? (Color){58, 66, 108, 255} : cls == 2 ? (Color){50, 58, 96, 255} : cls == 1 ? (Color){34, 40, 66, 255} : (Color){40, 46, 74, 255};
}
static Vector2 PedPos(Ped *p) {
  Edge *e = &E[p->e]; Vector2 c = NP(e->b), nrm = {-e->uy, e->ux}; float half = RW(e->cls) / 2 + 2;
  c = (Vector2){c.x - e->ux * 13, c.y - e->uy * 13};
  return (Vector2){c.x + nrm.x * (-half + 2 * half * p->t), c.y + nrm.y * (-half + 2 * half * p->t)};
}
static Bld *FindB(int type) { for (int b = 0; b < nBld; b++) if (bld[b].type == type) return &bld[b]; return NULL; }
static void PushEv(Ev *l, int *n, int *over, Color c, const char *t, const char *d, float frac) {
  if (*n >= 5) { (*over)++; return; }
  l[*n].c = c; snprintf(l[*n].t, 40, "%s", t); snprintf(l[*n].d, 40, "%s", d); l[*n].frac = frac; (*n)++;
}


/* ---------- header and KPI cards ---------- */
static void DrawHeader(void) {
  float pulse = .5f + .5f * sinf((float)GetTime() * 4); char b[16]; int act = (int)(GetTime() * .8) % 3;
  int hh = (int)(fmodf(clockS, 86400) / 3600), mm = (int)(fmodf(clockS, 3600) / 60);
  Color lc = paused ? C_AMBER : C_GREEN, lamp[3] = {C_RED, C_AMBER, C_GREEN}, ec[5] = {C_PINK, C_VIOLET, C_CYAN, C_AMBER, C_GREEN};
  Rectangle pill = {250, 28, paused ? 100 : 84, 28}, tc = {1076, 22, 176, 40};
  static const char *EV[5] = {"Crash", "Stadium", "Rain", "Works", "Market"}, *SP[3] = {"1x", "2x", "4x"};
  RR((Rectangle){28, 22, 40, 40}, 12, C_VIOLET); RR((Rectangle){39, 27, 18, 30}, 7, C_BG);
  for (int i = 0; i < 3; i++) DrawCircleV((Vector2){48, 34.0f + i * 8}, 3.4f, Fade(lamp[i], i == act ? 1.0f : .22f));
  Txt("Gridlock", 80, 17, 26, C_TEXT, 1, AL); Txt("Town traffic monitor", 80, 46, 13, C_MUTED, 0, AL);
  RR(pill, 14, Fade(lc, .14f)); DrawCircleV((Vector2){pill.x + 16, pill.y + 14}, 3.5f, lc);
  DrawRing((Vector2){pill.x + 16, pill.y + 14}, 5 + pulse * 3, 6 + pulse * 3, 0, 360, 24, Fade(lc, .5f * (1 - pulse)));
  Txt(paused ? "PAUSED" : "LIVE", pill.x + 30, pill.y + 7, 12, lc, 1, AL);
  snprintf(b, 16, "%02d:%02d", hh, mm); Txt(b, 520, 12, 30, C_TEXT, 1, AC);
  Txt(rain ? "Rain" : fogL > .5f ? "Fog" : "Clear skies", 520, 46, 12, C_MUTED, 0, AC);
  for (int i = 0; i < 5; i++) {
    Rectangle r = {660 + i * 82, 22, 76, 40};
    int on = (i == 0 && CrashOn()) || (i == 1 && stadiumT > 0) || (i == 2 && rain) || (i == 3 && WorksOn()) || (i == 4 && marketT > 0);
    RR(r, 20, Hover(r) || on ? ec[i] : Fade(ec[i], .18f)); Txt(EV[i], r.x + 38, r.y + 11, 14, Hover(r) || on ? WHITE : ec[i], 1, AC);
  }
  RR((Rectangle){tc.x - 1, tc.y - 1, tc.width + 2, tc.height + 2}, 21, C_BORDER); RR(tc, 20, C_CARD);
  for (int i = 0; i < 3; i++) {
    Rectangle t = {tc.x + 4 + i * 56, 26, 56, 32};
    if (i == speedIdx) RR(t, 16, C_VIOLET); else if (Hover(t)) RR(t, 16, Fade(WHITE, .06f));
    Txt(SP[i], t.x + 28, t.y + 8, 15, i == speedIdx ? WHITE : C_MUTED, i == speedIdx, AC);
  }
}
static void DeltaTxt(const char *l, float pct, int upIsGood, float x, float y) {
  char b[32]; Color c = fabsf(pct) < 1 ? C_MUTED : ((pct > 0) == (upIsGood != 0)) ? C_GREEN : C_PINK;
  snprintf(b, 32, "%s %+.0f%%", l, Clamp(pct, -999, 999)); Txt(b, x, y, 10, c, 1, AL);
}
static void DrawSignalCard(Rectangle r) {
  char b[48];
  Card(r, Hover(r) ? Fade(C_VIOLET, .75f) : C_BORDER);
  Txt("Traffic signals", r.x + 20, r.y + 14, 13, C_MUTED, 0, AL);
  snprintf(b, 48, "%.0f / %d on", kpiD[3], lightsTot); Txt(b, r.x + 20, r.y + 31, 24, lightsOn < lightsTot ? C_AMBER : C_TEXT, 1, AL);
  Txt("DIVERTED", r.x + r.width - 20, r.y + 14, 10, C_MUTED, 1, AR);
  snprintf(b, 48, "%d", divSig); Txt(b, r.x + r.width - 20, r.y + 26, 26, divSig ? C_VIOLET : C_TEXT, 1, AR);
  if (haveBase) {
    DeltaTxt("delay", (emaDelay - baseDelay) / fmaxf(baseDelay, .5f) * 100, 0, r.x + 18, r.y + 75);
    DeltaTxt("speed", (emaSpeed - baseSpeed) / fmaxf(baseSpeed, 1) * 100, 1, r.x + 84, r.y + 75);
    DeltaTxt("queue", (emaQueue - baseQueue) / fmaxf(baseQueue, 1) * 100, 0, r.x + 146, r.y + 75);
  } else Txt("T: all signals   L: hovered junction", r.x + 20, r.y + 74, 11, C_MUTED, 0, AL);
  if (Hover(r)) SetTip("Signal impact", haveBase ? "Changes since the last switch. Click: toggle all" : "Click to switch all signals off/on", GetMousePosition(), C_VIOLET);
}
static void DrawKpi(int i) {
  Rectangle r = {28 + i * 248, 88, 232, 100}; Color ac[5] = {C_CYAN, C_GREEN, C_PINK, C_VIOLET, C_AMBER}, pc;
  char b[48], p[32]; const char *sub; Rectangle pill; float v = kpiD[i], d = kpiRef[i] > 0.001f ? (kpiT[i] - kpiRef[i]) / kpiRef[i] * 100 : 0;
  if (i == 3) { DrawSignalCard(r); return; }
  Card(r, Hover(r) ? Fade(ac[i], .75f) : C_BORDER);
  Txt(KPI_N[i], r.x + 20, r.y + 16, 13, C_MUTED, 0, AL);
  if (i == 0) snprintf(b, 48, "%.0f", v); else if (i == 1) snprintf(b, 48, "%.0f km/h", v); else if (i == 2) snprintf(b, 48, "%.0f%%", v); else snprintf(b, 48, "%.2f t", v);
  Txt(b, r.x + 20, r.y + 34, 30, C_TEXT, 1, AL);
  if (i < 3) { snprintf(p, 32, "%+.1f%%", d); sub = "vs 30s ago"; pc = i == 0 ? C_CYAN : ((i == 1) == (d >= 0) ? C_GREEN : C_PINK); }
  else { snprintf(p, 32, "%.0f kg/h", co2Rate); sub = "right now"; pc = C_AMBER; }
  pill = (Rectangle){r.x + 20, r.y + 72, TW(p, 12, 1) + 20, 20}; RR(pill, 10, Fade(pc, .15f));
  Txt(p, pill.x + 10, pill.y + 3, 12, pc, 1, AL); Txt(sub, pill.x + pill.width + 8, pill.y + 4, 11, C_MUTED, 0, AL);
}

/* ---------- 2D town map ---------- */
static void DrawMap2D(int hn, int hb) {
  Rectangle r = R_MAP; float day = DayF(), dm = .55f + .45f * day, tt = (float)GetTime(), dtm = GetFrameTime(), rx = OX + 235;
  Color water = Mix((Color){18, 40, 80, 255}, (Color){40, 100, 170, 255}, day); Bld *st = FindB(BT_STAD);
  Card(r, C_BORDER); RR((Rectangle){r.x + 6, r.y + 6, r.width - 12, r.height - 12}, 12, Mix((Color){14, 26, 26, 255}, (Color){34, 62, 48, 255}, day));
  Txt("TOWN", r.x + 24, r.y + 18, 12, C_MUTED, 1, AL);
  Txt("click: building info / close road   ctrl+click: roadworks   shift+click: crash", r.x + r.width - 24, r.y + 18, 12, C_MUTED, 0, AR);
  RR((Rectangle){OX + 315, OY + 28, 125, 108}, 14, Mix((Color){18, 44, 34, 255}, (Color){52, 98, 62, 255}, day));
  RR((Rectangle){OX + 440, OY + 250, 200, 190}, 8, Fade((Color){110, 114, 130, 255}, .22f));
  for (int i = 0; i < 7; i++) { Vector2 a = {OX + RV[i][0], OY + RV[i][1]}, c = {OX + RV[i + 1][0], OY + RV[i + 1][1]}; DrawLineEx(a, c, 36, water); DrawCircleV(c, 18, water); }
  DrawCircleV((Vector2){OX + 380, OY + 70}, 27, water);
  RR((Rectangle){OX + 503, OY + 150, 87, 55}, 6, Mix((Color){60, 60, 74, 255}, (Color){150, 146, 138, 255}, day));
  for (int i = 0; i < nTree; i++) DrawCircleV((Vector2){trees[i].x, trees[i].y}, 3.4f * trees[i].z, Mix((Color){10, 30, 20, 255}, (Color){38, 108, 58, 255}, day));
  DrawLineEx((Vector2){rx, OY + 110}, (Vector2){rx, OY + 395}, 5, (Color){70, 72, 88, 255});
  for (float y = OY + 112; y < OY + 395; y += 9) DrawLineEx((Vector2){rx - 6, y}, (Vector2){rx + 6, y}, 2, (Color){52, 54, 66, 255});
  for (int e = 0; e < nE; e += 2) {
    Edge *q = &E[e]; Color rc = RoadCol(q->cls, q->bridge); Vector2 a = NP(q->a), u = {q->ux, q->uy}, nn = {-q->uy * RW(q->cls) / 2, q->ux * RW(q->cls) / 2};
    if (q->closed) rc = Mix(rc, C_RED, .35f);
    DrawLineEx(a, NP(q->b), RW(q->cls), rc);
    if (q->bridge) { DrawLineEx(Vector2Add(a, nn), Vector2Add(NP(q->b), nn), 2, (Color){225, 230, 245, 255}); DrawLineEx(Vector2Subtract(a, nn), Vector2Subtract(NP(q->b), nn), 2, (Color){225, 230, 245, 255}); }
    else if (q->cls >= 2) for (float d = 16; d + 7 < q->len - 14; d += 14) DrawLineEx(Vector2Add(a, Vector2Scale(u, d)), Vector2Add(a, Vector2Scale(u, d + 7)), 1.5f, Fade(WHITE, .3f));
  }
  for (int n = 0; n < NNODE; n++) DrawCircleV(NP(n), RW(N[n].maxcls) / 2, RoadCol(N[n].maxcls, 0));
  for (int e = 0; e < nE; e++) {
    float rt = E[e].ratio, ln = RW(E[e].cls) * .26f; Vector2 a = NP(E[e].a), n = {-E[e].uy * ln, E[e].ux * ln};
    Color cc = rt > .6f ? Mix(C_AMBER, C_GREEN, (rt - .6f) / .4f) : Mix(C_RED, C_AMBER, rt / .6f);
    Vector2 p0 = {a.x + E[e].ux * 10 + n.x, a.y + E[e].uy * 10 + n.y}, p1 = {a.x + E[e].ux * (E[e].len - 10) + n.x, a.y + E[e].uy * (E[e].len - 10) + n.y};
    DrawLineEx(p0, p1, 2.4f, E[e].closed ? Fade(C_MUTED, .25f) : Fade(cc, .7f));
  }
  for (int e = 0; e < nE; e += 2) {
    Vector2 m = Vector2Lerp(NP(E[e].a), NP(E[e].b), .5f);
    if (E[e].closed) { DrawLineEx((Vector2){m.x - 6, m.y - 6}, (Vector2){m.x + 6, m.y + 6}, 3, C_RED); DrawLineEx((Vector2){m.x - 6, m.y + 6}, (Vector2){m.x + 6, m.y - 6}, 3, C_RED); }
    if (E[e].works > 0) for (int k = 0; k < 5; k++) {
      Vector2 p = Vector2Lerp(NP(E[e].a), NP(E[e].b), .2f + k * .15f);
      DrawTriangle((Vector2){p.x, p.y - 6}, (Vector2){p.x - 4, p.y + 3}, (Vector2){p.x + 4, p.y + 3}, (Color){255, 120, 30, 255});
    }
  }
  for (int b = 0; b < nBld; b++) {
    Bld *q = &bld[b]; Color c = Mix(BLACK, BCol(q->type), dm); float ang = atan2f(q->fy, q->fx) * RAD2DEG; Vector2 p = {q->x, q->y};
    if (q->type == BT_STAD) { DrawEllipse((int)q->x, (int)q->y, q->w / 2, q->d / 2, c); DrawEllipse((int)q->x, (int)q->y, q->w / 2 - 9, q->d / 2 - 9, Mix(BLACK, (Color){60, 150, 90, 255}, dm)); }
    else if (q->type == BT_FOUNT) { DrawCircleV(p, 12, Mix(BLACK, (Color){160, 156, 150, 255}, dm)); DrawCircleV(p, 9, c); }
    else if (q->type == BT_MILL) { DrawCircleV(p, 8, c); for (int k = 0; k < 4; k++) { float a = tt * .8f + k * PI / 2; DrawLineEx(p, (Vector2){p.x + cosf(a) * 14, p.y + sinf(a) * 14}, 2, Mix(BLACK, WHITE, dm)); } }
    else DrawRectanglePro((Rectangle){q->x, q->y, q->w, q->d}, (Vector2){q->w / 2, q->d / 2}, ang, c);
    if (q->type == BT_HOSP) { DrawRectangle((int)q->x - 2, (int)q->y - 7, 4, 14, C_RED); DrawRectangle((int)q->x - 7, (int)q->y - 2, 14, 4, C_RED); }
    if (q->type == BT_MARKET) for (int k = 0; k < 6; k++) DrawRectangle((int)(q->x - 30 + k * 11), (int)q->y - 5, 8, 10, k % 2 ? Mix(BLACK, C_PINK, dm) : Mix(BLACK, C_AMBER, dm));
    if (b == selB || b == hb) DrawRing(p, .5f * hypotf(q->w, q->d) + 3, .5f * hypotf(q->w, q->d) + 5, 0, 360, 28, b == selB ? WHITE : Fade(WHITE, .5f));
  }
  for (int n = 0; n < NNODE; n++) if (N[n].sig) { /* signal heads on each approach */
    for (int e = 0; e < nE; e++) if (E[e].b == n) {
      int s = Sig(n, E[e].horiz); Color c = s == 4 ? (((int)(tt * 2) % 2) ? C_AMBER : Fade(C_AMBER, .2f)) : SigCol(s);
      DrawCircleV((Vector2){N[n].x - E[e].ux * 9, N[n].y - E[e].uy * 9}, 2.5f, c);
    }
    if (!N[n].on) DrawRing(NP(n), 11, 12.5f, 0, 360, 24, Fade(C_AMBER, .5f + .4f * sinf(tt * 6)));
  }
  { Vector2 c = NP(17); float a = barPos; /* level crossing */
    DrawLineEx((Vector2){c.x - 11, c.y - 14}, (Vector2){c.x - 11, c.y - 14 + 14 * a}, 3, a > .5f ? C_RED : C_MUTED);
    DrawLineEx((Vector2){c.x + 11, c.y + 14}, (Vector2){c.x + 11, c.y + 14 - 14 * a}, 3, a > .5f ? C_RED : C_MUTED);
    if (barrierDown && ((int)(tt * 3) % 2)) { DrawCircleV((Vector2){c.x - 11, c.y - 16}, 3, C_RED); DrawCircleV((Vector2){c.x + 11, c.y + 16}, 3, C_RED); }
    for (int k = 0; k < 4; k++) DrawRectangle((int)rx - 5, (int)(trainY - 32 + k * 16), 10, 14, k == 0 ? C_RED : (Color){150, 160, 190, 255});
  }
  for (int i = 0; i < nPed; i++) if (ped[i].t > .01f && ped[i].t < .99f) DrawCircleV(PedPos(&ped[i]), 2, WHITE);
  for (int i = 0; i < NCAR; i++) if (cars[i].on) {
    Edge *e = &E[cars[i].edge]; float ln = RW(e->cls) * .26f; Vector2 a = NP(e->a), p = {a.x + e->ux * cars[i].pos - e->uy * ln, a.y + e->uy * cars[i].pos + e->ux * ln};
    Color c = Mix(C_PINK, C_CYAN, cars[i].v / e->limit); float rad = cars[i].type == 2 ? 3.8f : cars[i].type == 1 ? 3.0f : 2.4f;
    if (cars[i].div > 0) { c = Mix(C_VIOLET, WHITE, .3f); DrawRing(p, 5, 6.5f, 0, 360, 16, Fade(C_VIOLET, Clamp(cars[i].div / 15, 0, 1))); }
    DrawCircleV(p, rad * 2.3f, Fade(c, .12f)); DrawCircleV(p, rad, c);
  }
  for (int e = 0; e < nE; e++) if (E[e].crash > 0) {
    Vector2 m = Vector2Lerp(NP(E[e].a), NP(E[e].b), .5f); int f = sinf(tt * 12) > 0;
    DrawCircleV(m, 16, Fade(f ? C_RED : C_CYAN, .22f)); DrawCircleV(m, 5, f ? C_RED : C_CYAN); DrawCircleV(m, 2, WHITE);
  }
  for (int k = 0; k < NAMB; k++) { /* ambulances */
    Amb *a = &amb[k]; Vector2 q; Color f = sinf(tt * 14 + k) > 0 ? C_RED : C_CYAN; float ph = fmodf(tt * 14, 10);
    if (a->st == 1 || a->st == 3) {
      Edge *e = &E[a->edge]; Vector2 sv = NP(e->a);
      q = (Vector2){sv.x + e->ux * a->pos - e->uy * 3, sv.y + e->uy * a->pos + e->ux * 3};
      DrawRing(q, 6 + ph, 7 + ph, 0, 360, 24, Fade(f, .35f));
    } else { Vector2 b = NP(a->node); q = (Vector2){b.x + 14 + k * 8, b.y + 14}; }
    if (a->st) DrawCircleV(q, 8, Fade(f, .28f));
    DrawCircleV(q, 4.2f, WHITE); DrawCircleV(q, 1.6f, f);
  }
  if (st) { Vector2 sp = {st->x, st->y}; float pu = .5f + .5f * sinf(tt * 4);
    if (stadiumT > 0) {
      float rem = stadiumT * CLOCKX, endc = fmodf(clockS + rem, 86400), w; char l2[48];
      DrawRing(sp, 36 + pu * 4, 38 + pu * 4, 0, 360, 48, Fade(C_VIOLET, .4f));
      DrawRing(sp, 33, 36, -90, -90 + 360 * (stadiumT / 90.0f), 48, C_VIOLET);
      snprintf(l2, 48, "ends %02d:%02d  (%d min left)", (int)(endc / 3600), (int)(fmodf(endc, 3600) / 60), (int)ceilf(rem / 60));
      w = fmaxf(TW("STADIUM EVENT", 11, 1), TW(l2, 11, 0)) + 20;
      RR((Rectangle){sp.x - w / 2, sp.y - 74, w, 36}, 8, (Color){28, 20, 58, 235});
      Txt("STADIUM EVENT", sp.x - w / 2 + 10, sp.y - 70, 11, C_VIOLET, 1, AL); Txt(l2, sp.x - w / 2 + 10, sp.y - 54, 11, C_TEXT, 0, AL);
    } else Txt("stadium", sp.x, sp.y + 34, 10, Fade(C_VIOLET, .9f), 0, AC);
  }
  if (rain) for (int i = 0; i < NDROP; i++) {
    drops[i].y += 420 * dtm; drops[i].x -= 80 * dtm;
    if (drops[i].y > r.y + r.height - 10) { drops[i].y = r.y + 8; drops[i].x = r.x + rnd() * r.width; }
    if (drops[i].x < r.x + 8) drops[i].x = r.x + r.width - 8;
    DrawLineEx(drops[i], (Vector2){drops[i].x - 2, drops[i].y + 8}, 1.2f, Fade(C_CYAN, .3f));
  }
  if (fogL > .05f) DrawRectangle((int)r.x + 6, (int)r.y + 6, (int)r.width - 12, (int)r.height - 12, Fade((Color){190, 196, 208, 255}, .30f * fogL));
  if (hn >= 0) DrawRing(NP(hn), 13, 15, 0, 360, 32, Fade(WHITE, .6f));
}

static void MapTips(int hn, int he, int hb) {
  char a[64], b[64]; Vector2 m = GetMousePosition();
  if (hn >= 0) {
    Node *n = &N[hn]; NName(hn, a);
    if (n->lc) snprintf(b, 64, "Level crossing - %s", barrierDown ? "barrier DOWN (train)" : "open");
    else if (n->sig) snprintf(b, 64, "Signals %s, cycle %.0fs, %.0f waiting  (L: toggle)", n->on ? "ON" : "OFF", n->cycle, n->q);
    else snprintf(b, 64, "Give-way junction, %.0f waiting", n->q);
    SetTip(a, b, m, n->sig && !n->on ? C_AMBER : C_CYAN);
  } else if (hb >= 0) {
    snprintf(a, 64, "%s", TYPE_N[bld[hb].type]); snprintf(b, 64, "Click to see the trips it generates");
    SetTip(a, b, m, BCol(bld[hb].type));
  } else if (he >= 0) {
    Edge *q = &E[he];
    if (q->closed) snprintf(b, 64, "CLOSED - click to reopen");
    else if (q->works > 0) snprintf(b, 64, "Roadworks - %d min left", (int)ceilf(q->works * CLOCKX / 60));
    else snprintf(b, 64, "%.0f km/h limit, %d cars%s", q->limit, q->cnt + E[he ^ 1].cnt, q->bridge ? "  (chokepoint)" : "");
    SetTip(q->nm, b, m, q->closed ? C_RED : q->works > 0 ? C_AMBER : C_CYAN);
  }
}

static void DrawInfo(void) {
  Rectangle r = {R_MAP.x + 14, R_MAP.y + R_MAP.height - 112, 360, 96}; Bld *b; char t[80], l1[96], l2[96], l3[96]; Color c;
  if (selB < 0) return;
  b = &bld[selB]; c = BCol(b->type);
  snprintf(t, 80, "%s", TYPE_N[b->type]); l1[0] = l2[0] = l3[0] = 0;
  switch (b->type) {
    case BT_HOME: snprintf(l1, 96, "Generates %d trips today", b->gen); snprintf(l2, 96, "work %d | industry %d | school run %d | shops %d", b->pg[0], b->pg[1], b->pg[2], b->pg[3]);
      snprintf(l3, 96, "Peaks: commute 08:00, school run 08:30, shops 10:30"); break;
    case BT_SHOP: snprintf(l1, 96, "Attracts %d shoppers, %d trips home today", b->att, b->gen); snprintf(l2, 96, "Busiest at 10:30 and 16:00"); break;
    case BT_OFFICE: snprintf(l1, 96, "Attracts %d commuters, %d left today", b->att, b->gen); snprintf(l2, 96, "Arrivals peak 08:00, departures 17:30"); break;
    case BT_SCHOOL: snprintf(l1, 96, "School run: %d drop-offs, %d pick-ups", b->att, b->gen); snprintf(l2, 96, "Drop-off 08:30, pick-up 15:20 (sharp peaks)"); break;
    case BT_IND: snprintf(l1, 96, "Shift workers: %d in, %d out today", b->att, b->gen); snprintf(l2, 96, "Shifts change 06:45 and 15:00"); break;
    case BT_STAD: snprintf(l1, 96, "Event crowds: %d arrivals today", b->att); snprintf(l2, 96, stadiumT > 0 ? "MATCH ON - supporters pouring in" : "Press S (or Stadium) for a match day"); break;
    case BT_HOSP: snprintf(l1, 96, "Ambulance base and destination"); snprintf(l2, 96, "Ambulance calls today: %d (E toggles response)", calls); break;
    case BT_MARKET: snprintf(l1, 96, "Market-day shoppers today: %d", b->att); snprintf(l2, 96, marketT > 0 ? "MARKET DAY - high street is crowded" : "Press M for market day"); break;
    case BT_MILL: snprintf(l1, 96, "An old windmill. Pure scenery."); snprintf(l2, 96, "It does not generate any traffic."); break;
    case BT_FOUNT: snprintf(l1, 96, "The town-square fountain"); snprintf(l2, 96, "Shoppers gather here on market day."); break;
    default: snprintf(l1, 96, "Railway station"); snprintf(l2, 96, "A train crosses the high street every ~90 s."); break;
  }
  RR((Rectangle){r.x - 1, r.y - 1, r.width + 2, r.height + 2}, 13, C_BORDER); RR(r, 12, (Color){14, 18, 34, 240});
  RR((Rectangle){r.x + 12, r.y + 12, 4, 20}, 2, c);
  Txt(t, r.x + 26, r.y + 10, 15, C_TEXT, 1, AL); Txt("click empty ground to close", r.x + r.width - 14, r.y + 12, 10, C_MUTED, 0, AR);
  Txt(l1, r.x + 16, r.y + 38, 13, C_TEXT, 1, AL); Txt(l2, r.x + 16, r.y + 57, 12, C_MUTED, 0, AL); Txt(l3, r.x + 16, r.y + 74, 12, C_MUTED, 0, AL);
}

static void DrawEvents(void) {
  Rectangle r = R_CHART; Ev ev[5]; int n = 0, over = 0, closed = 0, off = 0; char t[40], d[40], a[8], b[8];
  if (stadiumT > 0) {
    float rem = stadiumT * CLOCKX, endc = fmodf(clockS + rem, 86400);
    snprintf(d, 40, "%d min left (ends %02d:%02d)", (int)ceilf(rem / 60), (int)(endc / 3600), (int)(fmodf(endc, 3600) / 60));
    PushEv(ev, &n, &over, C_VIOLET, "Stadium event", d, stadiumT / 90.0f);
  }
  if (marketT > 0) { snprintf(d, 40, "%d min left", (int)ceilf(marketT * CLOCKX / 60)); PushEv(ev, &n, &over, C_GREEN, "Market day in the square", d, marketT / 90.0f); }
  for (int e = 0; e < nE; e++) if (E[e].crash > 0) {
    NName(E[e].a, a); NName(E[e].b, b); snprintf(t, 40, "%s on %s > %s", E[e].bridge ? "Bridge crash" : "Crash", a, b);
    snprintf(d, 40, "%sclears in %d min", E[e].resp == 3 ? "minor, " : "", (int)ceilf(E[e].crash * CLOCKX / 60));
    PushEv(ev, &n, &over, C_RED, t, d, E[e].crash / 70.0f);
  }
  for (int e = 0; e < nE; e += 2) if (E[e].works > 0) {
    NName(E[e].a, a); NName(E[e].b, b); snprintf(t, 40, "Roadworks %s - %s", a, b); snprintf(d, 40, "%d min left", (int)ceilf(E[e].works * CLOCKX / 60));
    PushEv(ev, &n, &over, C_AMBER, t, d, E[e].works / 120.0f);
  }
  for (int e = 0; e < nE; e += 2) if (E[e].closed) closed++;
  if (closed) { snprintf(t, 40, "%d road%s closed", closed, closed > 1 ? "s" : ""); PushEv(ev, &n, &over, C_PINK, t, "click to reopen", -1); }
  for (int i = 0; i < NNODE; i++) if (N[i].sig && !N[i].on) off++;
  if (off) { snprintf(t, 40, "Signals off at %d junction%s", off, off > 1 ? "s" : ""); snprintf(d, 40, "%d cars diverted", divSig); PushEv(ev, &n, &over, C_AMBER, t, d, -1); }
  if (barrierDown) PushEv(ev, &n, &over, C_RED, "Level crossing closed", "train passing", -1);
  if (fogL > .5f) PushEv(ev, &n, &over, C_MUTED, "Fog", "speeds -12%", -1);
  if (rain) PushEv(ev, &n, &over, C_CYAN, "Rain", "speeds -18%, demand +8%", -1);
  Card(r, C_BORDER); Txt("ACTIVE EVENTS", r.x + 24, r.y + 18, 12, C_MUTED, 1, AL);
  if (n) { snprintf(d, 40, "%d ACTIVE", n + over); Txt(d, r.x + r.width - 24, r.y + 18, 12, C_AMBER, 1, AR); }
  else {
    DrawRing((Vector2){r.x + r.width / 2, r.y + 80}, 16, 18, 0, 360, 40, Fade(C_GREEN, .6f)); DrawCircleV((Vector2){r.x + r.width / 2, r.y + 80}, 5, C_GREEN);
    Txt("All quiet", r.x + r.width / 2, r.y + 108, 18, C_TEXT, 1, AC);
    Txt("Try C, S, R, W, M, T or O to stir things up", r.x + r.width / 2, r.y + 134, 12, C_MUTED, 0, AC);
  }
  for (int i = 0; i < n; i++) {
    float y = r.y + 46 + i * 28;
    RR((Rectangle){r.x + 24, y, 4, 17}, 2, ev[i].c);
    Txt(ev[i].t, r.x + 38, y - 1, 13, C_TEXT, 1, AL); Txt(ev[i].d, r.x + r.width - 24, y, 12, C_MUTED, 0, AR);
    if (ev[i].frac >= 0) { RR((Rectangle){r.x + 38, y + 19, r.width - 62, 3}, 1.5f, Fade(WHITE, .07f)); RR((Rectangle){r.x + 38, y + 19, fmaxf(3, (r.width - 62) * ev[i].frac), 3}, 1.5f, ev[i].c); }
  }
}
static void DrawPurpose(void) { /* live trips by purpose: fixed rows, calm bars */
  Rectangle r = R_HOT; static float scaleMax = 24; float mx = 0, tot = 0; char b[48];
  static const char *NM[7] = {"Commuting to work", "Industry shifts", "School run", "Shopping", "Stadium crowd", "Market trips", "Heading home"};
  static const char *TIP[7] = {"Home to offices. Peaks around 08:00", "Home to the industrial units (06:45, 15:00)", "Home to school. Peaks 08:30",
                               "Home to the shops. Peaks 10:30, 16:00", "Supporters heading to the stadium (S)", "Shoppers heading to the market (M)", "Return trips: 17:30 rush, 15:20 school pick-up"};
  Color PC[7] = {C_CYAN, (Color){150, 160, 190, 255}, C_GREEN, C_AMBER, C_VIOLET, C_PINK, (Color){110, 150, 255, 255}};
  for (int i = 0; i < 7; i++) { mx = fmaxf(mx, purD[i]); tot += purD[i]; }
  scaleMax = Appr(scaleMax, fmaxf(24, mx * 1.2f), .4f, GetFrameTime());
  Card(r, C_BORDER); Txt("TRIPS RIGHT NOW", r.x + 24, r.y + 18, 12, C_MUTED, 1, AL);
  snprintf(b, 48, "%.0f cars on trips", tot); Txt(b, r.x + r.width - 24, r.y + 18, 12, C_TEXT, 1, AR);
  for (int i = 0; i < 7; i++) {
    float y = r.y + 42 + i * 20, w = r.width - 220, bw = Clamp(purD[i] / scaleMax, 0, 1) * w; Rectangle row = {r.x + 12, y - 3, r.width - 24, 20};
    if (Hover(row)) { RR(row, 6, Fade(WHITE, .04f)); SetTip(NM[i], TIP[i], GetMousePosition(), PC[i]); }
    RR((Rectangle){r.x + 24, y + 2, 4, 12}, 2, PC[i]); Txt(NM[i], r.x + 38, y, 12, C_TEXT, 1, AL);
    RR((Rectangle){r.x + 160, y + 4, w, 8}, 4, Fade(WHITE, .06f)); if (purD[i] > .3f) RR((Rectangle){r.x + 160, y + 4, fmaxf(4, bw), 8}, 4, PC[i]);
    snprintf(b, 48, "%.0f", purD[i]); Txt(b, r.x + r.width - 24, y, 12, C_TEXT, 1, AR);
  }
}
static void Glow(float x, float y, float rad, Color c, float peak) {
  for (int i = 0; i < 14; i++) DrawCircleV((Vector2){x, y}, rad * (1 - i / 14.0f), Fade(c, peak / 14));
}

static void DrawEmerg(void) {
  Rectangle r = R_FEED; char b[64], c[64], n1[8], n2[8], v[3][24]; int busy = 0, waiting = 0;
  static const char *ST[4] = {"Available", "En route", "On scene", "To hospital"}, *L[3] = {"AVG RESPONSE", "CALLS", "WAITING"};
  Color SC[4] = {C_GREEN, C_AMBER, C_RED, C_CYAN}; float xs[3] = {r.x + 24, r.x + 160, r.x + 260};
  for (int k = 0; k < NAMB; k++) if (amb[k].st) busy++;
  for (int e = 0; e < nE; e++) if (E[e].resp == 1 && E[e].crash > 0 && emgOn) waiting++;
  Card(r, C_BORDER); Txt("EMERGENCY SERVICES", r.x + 24, r.y + 18, 12, C_MUTED, 1, AL);
  if (emgOn) snprintf(b, 64, "%d of %d units busy", busy, NAMB); else snprintf(b, 64, "RESPONSE OFF (press E)");
  Txt(b, r.x + r.width - 24, r.y + 18, 12, emgOn ? C_GREEN : C_AMBER, 1, AR);
  for (int k = 0; k < NAMB; k++) {
    Amb *a = &amb[k]; float y = r.y + 40 + k * 23; c[0] = 0;
    RR((Rectangle){r.x + 24, y + 1, 4, 15}, 2, SC[a->st]);
    snprintf(b, 64, "Unit %d", k + 1); Txt(b, r.x + 38, y, 13, C_TEXT, 1, AL); Txt(ST[a->st], r.x + 100, y + 1, 12, SC[a->st], 0, AL);
    if (a->st == 1 || a->st == 3) {
      Edge *e = &E[a->edge]; int n = e->b, hi = 0;
      float rem = (e->len - a->pos) / (e->limit * PXK) + (n == a->dst ? 0 : pathT[n][a->dst] / PXK); int mins = (int)ceilf(rem / 1.1f * CLOCKX / 60);
      for (int h = 0; h < NHOSP; h++) if (HN_[h] == a->dst) hi = h;
      if (a->st == 1) { NName(E[a->call].a, n1); NName(E[a->call].b, n2); snprintf(c, 64, "crash %s > %s, ETA %d min", n1, n2, mins); }
      else snprintf(c, 64, "hospital %d, ETA %d min", hi + 1, mins);
    } else if (a->st == 2) snprintf(c, 64, "treating, %d min left", (int)ceilf(a->onScene * CLOCKX / 60));
    else snprintf(c, 64, "at hospital %d", a->hosp + 1);
    Txt(c, r.x + r.width - 24, y + 1, 12, C_MUTED, 0, AR);
  }
  if (respN) snprintf(v[0], 24, "%.1f min", respSum / respN / 60); else snprintf(v[0], 24, "--");
  snprintf(v[1], 24, "%d", calls); snprintf(v[2], 24, "%d", waiting);
  for (int i = 0; i < 3; i++) { Txt(L[i], xs[i], r.y + 114, 10, C_MUTED, 1, AL); Txt(v[i], xs[i], r.y + 127, 14, C_TEXT, 1, AL); }
}

static void DrawViewToggle(void) {
  Rectangle t = {R_MAP.x + 132, R_MAP.y + 10, 96, 26}; static const char *L[2] = {"2D", "3D"};
  RR((Rectangle){t.x - 1, t.y - 1, t.width + 2, t.height + 2}, 14, C_BORDER); RR(t, 13, C_BG);
  for (int i = 0; i < 2; i++) {
    Rectangle h = {t.x + 3 + i * 45, t.y + 3, 45, 20}; int on = (i == 1) == (view3d != 0);
    if (on) RR(h, 10, C_VIOLET); else if (Hover(h)) RR(h, 10, Fade(WHITE, .06f));
    Txt(L[i], h.x + 22, h.y + 3, 12, on ? WHITE : C_MUTED, on, AC);
  }
}

static void DrawOverlay(void) {
  if (toastT > 0) {
    float a = Clamp(fminf(toastT, 3.0f - toastT) * 4, 0, 1), w = TW(toastMsg, 15, 1) + 64; Rectangle t = {SW / 2 - w / 2, 66 - 60 * (1 - a), w, 38};
    RR((Rectangle){t.x, t.y + 3, w, 38}, 19, Fade(BLACK, .35f)); RR(t, 19, Mix(C_PINK, C_VIOLET, .4f));
    DrawCircleV((Vector2){t.x + 22, t.y + 19}, 4, WHITE); Txt(toastMsg, t.x + 38, t.y + 10, 15, WHITE, 1, AL);
  }
  if (tip.on) {
    float w = fmaxf(TW(tip.a, 14, 1), TW(tip.b, 12, 0)) + 34, h = 50, x = tip.p.x + 16, y = tip.p.y - h - 12;
    if (x + w > SW - 8) x = tip.p.x - w - 16;
    if (y < 8) y = tip.p.y + 18;
    RR((Rectangle){x, y + 4, w, h}, 10, Fade(BLACK, .4f)); RR((Rectangle){x - 1, y - 1, w + 2, h + 2}, 11, C_BORDER); RR((Rectangle){x, y, w, h}, 10, (Color){28, 33, 58, 250});
    RR((Rectangle){x + 11, y + 11, 3, h - 22}, 1.5f, tip.c); Txt(tip.a, x + 22, y + 9, 14, C_TEXT, 1, AL); Txt(tip.b, x + 22, y + 28, 12, C_MUTED, 0, AL);
  }
}


/* ====================== 3D VIEW ====================== */
static Shader sh3;
static int lSun, lSunC, lAmb, lCam, lFogC, lFogD, lPl, lPlc;
static Camera3D cam3;
static Ray ray3;
static Vector3 splash[NSPL], strollP[14];
static Vector2 strollT[14];
static const char *PRESET[4] = {"Free", "Top-down", "Cinematic", "Chase"};

static const char *VS3 =
  "#version 330\n"
  "in vec3 vertexPosition;\n"
  "in vec4 vertexColor;\n"
  "uniform mat4 mvp;\n"
  "out vec3 fPos;\n"
  "out vec4 fCol;\n"
  "void main(){ fPos = vertexPosition; fCol = vertexColor; gl_Position = mvp*vec4(vertexPosition,1.0); }\n";
static const char *FS3 =
  "#version 330\n"
  "in vec3 fPos; in vec4 fCol; out vec4 outCol;\n"
  "uniform vec3 sunDir; uniform vec3 sunCol; uniform vec3 ambCol; uniform vec3 camPos; uniform vec3 fogCol; uniform float fogDen;\n"
  "uniform vec4 pl[12]; uniform vec3 plc[12];\n"
  "void main(){\n"
  "  vec3 n = normalize(cross(dFdx(fPos), dFdy(fPos)));\n"
  "  vec3 v = normalize(camPos - fPos); if (dot(n, v) < 0.0) n = -n;\n"
  "  vec3 lit = ambCol + sunCol * max(dot(n, -sunDir), 0.0);\n"
  "  for (int i = 0; i < 12; i++) {\n"
  "    vec3 d = pl[i].xyz - fPos; float dist = length(d) + 0.001;\n"
  "    float att = clamp(1.0 - dist / max(pl[i].w, 0.01), 0.0, 1.0); att *= att;\n"
  "    lit += plc[i] * att * (0.35 + 0.65 * max(dot(n, d / dist), 0.0));\n"
  "  }\n"
  "  vec3 col = fCol.rgb * lit;\n"
  "  float dd = length(camPos - fPos) * fogDen;\n"
  "  col = mix(col, fogCol, clamp(1.0 - exp(-dd * dd), 0.0, 1.0));\n"
  "  outCol = vec4(col, fCol.a);\n"
  "}\n";

static Vector3 W3(float px, float py, float y) { return (Vector3){(px - cx3) / 10.0f, y, (py - cy3) / 10.0f}; }
static void Tri3(Vector3 a, Vector3 b, Vector3 c, Color k) {
  rlColor4ub(k.r, k.g, k.b, k.a); rlVertex3f(a.x, a.y, a.z); rlVertex3f(b.x, b.y, b.z); rlVertex3f(c.x, c.y, c.z);
}
static void Quad3(Vector3 a, Vector3 b, Vector3 c, Vector3 d, Color k) { rlBegin(RL_TRIANGLES); Tri3(a, b, c, k); Tri3(a, c, d, k); rlEnd(); }
static void RectQ(float x0, float y0, float x1, float y1, float y, Color k) { Quad3(W3(x0, y0, y), W3(x1, y0, y), W3(x1, y1, y), W3(x0, y1, y), k); }
static void Ribbon(float x0, float z0, float x1, float z1, float w, float y, Color k) {
  float dx = x1 - x0, dz = z1 - z0, l = sqrtf(dx * dx + dz * dz) + 1e-6f, nx = -dz / l * w / 2, nz = dx / l * w / 2;
  Quad3((Vector3){x0 - nx, y, z0 - nz}, (Vector3){x1 - nx, y, z1 - nz}, (Vector3){x1 + nx, y, z1 + nz}, (Vector3){x0 + nx, y, z0 + nz}, k);
}
static Vector3 PL(Vector3 c, float fx, float fz, float sf, float sr, float L, float W, float y) {
  return (Vector3){c.x + fx * sf * L / 2 - fz * sr * W / 2, y, c.z + fz * sf * L / 2 + fx * sr * W / 2};
}
static void OBox(Vector3 c, float fx, float fz, float L, float H, float W, Color k) { /* oriented box; c is the centre */
  static const int F[5][4] = {{4, 5, 7, 6}, {0, 1, 5, 4}, {2, 3, 7, 6}, {0, 2, 6, 4}, {1, 3, 7, 5}};
  Vector3 p[8];
  for (int i = 0; i < 8; i++) p[i] = PL(c, fx, fz, (i & 1) ? 1 : -1, (i & 2) ? 1 : -1, L, W, (i & 4) ? c.y + H / 2 : c.y - H / 2);
  rlBegin(RL_TRIANGLES);
  for (int f = 0; f < 5; f++) { Tri3(p[F[f][0]], p[F[f][1]], p[F[f][2]], k); Tri3(p[F[f][0]], p[F[f][2]], p[F[f][3]], k); }
  rlEnd();
}
static void RoofP(Vector3 c, float fx, float fz, float L, float W, float rh, Color k) { /* pitched roof, c at eave height */
  float y0 = c.y, y1 = c.y + rh; Color g = Mix(k, BLACK, .2f);
  rlBegin(RL_TRIANGLES);
  Tri3(PL(c, fx, fz, -1, -1, L, W, y0), PL(c, fx, fz, 1, -1, L, W, y0), PL(c, fx, fz, 1, 0, L, W, y1), k); Tri3(PL(c, fx, fz, -1, -1, L, W, y0), PL(c, fx, fz, 1, 0, L, W, y1), PL(c, fx, fz, -1, 0, L, W, y1), k);
  Tri3(PL(c, fx, fz, -1, 1, L, W, y0), PL(c, fx, fz, 1, 1, L, W, y0), PL(c, fx, fz, 1, 0, L, W, y1), k); Tri3(PL(c, fx, fz, -1, 1, L, W, y0), PL(c, fx, fz, 1, 0, L, W, y1), PL(c, fx, fz, -1, 0, L, W, y1), k);
  Tri3(PL(c, fx, fz, 1, -1, L, W, y0), PL(c, fx, fz, 1, 1, L, W, y0), PL(c, fx, fz, 1, 0, L, W, y1), g);
  Tri3(PL(c, fx, fz, -1, -1, L, W, y0), PL(c, fx, fz, -1, 1, L, W, y0), PL(c, fx, fz, -1, 0, L, W, y1), g);
  rlEnd();
}
static void ShadowPoly(Vector2 *pt, int n, float y, Color k) { /* convex hull (gift wrapping) filled as a fan */
  Vector2 h[16]; int m = 0, s = 0, cur;
  for (int i = 1; i < n; i++) if (pt[i].x < pt[s].x || (pt[i].x == pt[s].x && pt[i].y < pt[s].y)) s = i;
  cur = s;
  do {
    int nx = (cur + 1) % n; h[m++] = pt[cur];
    for (int i = 0; i < n; i++) { float cr = (pt[nx].x - pt[cur].x) * (pt[i].y - pt[cur].y) - (pt[nx].y - pt[cur].y) * (pt[i].x - pt[cur].x); if (cr < 0) nx = i; }
    cur = nx;
  } while (cur != s && m < 15);
  rlBegin(RL_TRIANGLES);
  for (int i = 1; i + 1 < m; i++) Tri3((Vector3){h[0].x, y, h[0].y}, (Vector3){h[i].x, y, h[i].y}, (Vector3){h[i + 1].x, y, h[i + 1].y}, k);
  rlEnd();
}
static void ShadowBox(float cx, float cz, float fx, float fz, float L, float W, float h, Vector2 sh, Color k) {
  Vector2 pt[8], off = {sh.x * h, sh.y * h}; float ol = Vector2Length(off);
  if (ol > .7f) off = Vector2Scale(off, .7f / ol); /* a short soft shade, not a long cast shadow */
  if (ol < .05f) off = (Vector2){.05f, .03f};
  for (int i = 0; i < 4; i++) {
    float sf = (i & 1) ? 1 : -1, sr = (i & 2) ? 1 : -1, x = cx + fx * sf * L / 2 - fz * sr * W / 2, z = cz + fz * sf * L / 2 + fx * sr * W / 2;
    pt[i] = (Vector2){x, z}; pt[i + 4] = (Vector2){x + off.x, z + off.y};
  }
  ShadowPoly(pt, 8, .145f, k);
}
static void WinFace(Vector3 c, float nx, float nz, float faceW, float H, float y0, unsigned seed, float nf, float sp) {
  float tx = -nz, tz = nx; int cols = (int)(faceW / sp);
  for (int ci = 0; ci < cols; ci++) for (float y = y0; y < H - .35f; y += .8f) {
    float u = (ci + .5f - cols / 2.0f) * sp, px = c.x + nx * .02f + tx * u, pz = c.z + nz * .02f + tz * u;
    unsigned hs = (seed * 2654435761u + (unsigned)ci * 40503u + (unsigned)(y * 10) * 9973u) >> 5;
    Color col = (nf > .35f && (hs % 100) < 55) ? (Color){255, 214, 130, 255} : (Color){34, 50, 78, 255};
    Quad3((Vector3){px - tx * .26f, y, pz - tz * .26f}, (Vector3){px + tx * .26f, y, pz + tz * .26f}, (Vector3){px + tx * .26f, y + .42f, pz + tz * .26f}, (Vector3){px - tx * .26f, y + .42f, pz - tz * .26f}, col);
  }
}
static void AddPL(float (*pl)[4], float (*plc)[3], int *np, Vector3 p, float rad, float r, float g, float b) {
  if (*np >= 12) return;
  pl[*np][0] = p.x; pl[*np][1] = p.y; pl[*np][2] = p.z; pl[*np][3] = rad; plc[*np][0] = r; plc[*np][1] = g; plc[*np][2] = b; (*np)++;
}
static Vector3 CarWorld(Car *c, float *fx, float *fz, float y) {
  Edge *e = &E[c->edge]; float ln = RW(e->cls) * .26f; Vector2 a = NP(e->a);
  *fx = e->ux; *fz = e->uy;
  return W3(a.x + e->ux * c->pos - e->uy * ln, a.y + e->uy * c->pos + e->ux * ln, y);
}
static Vector3 AmbWorld(Amb *a, int k, float *fx, float *fz) {
  if (a->st == 1 || a->st == 3) { Edge *e = &E[a->edge]; Vector2 s = NP(e->a); *fx = e->ux; *fz = e->uy; return W3(s.x + e->ux * a->pos - e->uy * 3, s.y + e->uy * a->pos + e->ux * 3, .3f); }
  { Vector2 b = NP(a->node); *fx = 1; *fz = 0; return W3(b.x + 14 + k * 8, b.y + 14, .3f); }
}

static void Init3D(void) {
  sh3 = LoadShaderFromMemory(VS3, FS3);
  lSun = GetShaderLocation(sh3, "sunDir"); lSunC = GetShaderLocation(sh3, "sunCol"); lAmb = GetShaderLocation(sh3, "ambCol"); lCam = GetShaderLocation(sh3, "camPos");
  lFogC = GetShaderLocation(sh3, "fogCol"); lFogD = GetShaderLocation(sh3, "fogDen"); lPl = GetShaderLocation(sh3, "pl"); lPlc = GetShaderLocation(sh3, "plc");
  rlSetClipPlanes(0.3, 600.0);
  cam3 = (Camera3D){.position = {0, 50, 50}, .target = {0, 0, 0}, .up = {0, 1, 0}, .fovy = 45, .projection = CAMERA_PERSPECTIVE};
  rt3 = LoadRenderTexture(1528, 1028); SetTextureFilter(rt3.texture, TEXTURE_FILTER_BILINEAR);
  for (int i = 0; i < NSPL; i++) splash[i] = (Vector3){0, 0, 9};
  for (int i = 0; i < 14; i++) { strollP[i] = W3(OX + 545 + (rnd() - .5f) * 70, OY + 177 + (rnd() - .5f) * 40, 0); strollT[i] = (Vector2){strollP[i].x, strollP[i].z}; }
}

static int FollowPt(Vector3 *cp, float *ty) { /* follow target: an ambulance on the move, else a car */
  if (followAmb >= 0) {
    Amb *a = &amb[followAmb];
    if (a->st == 1 || a->st == 3) { float fx, fz; *cp = AmbWorld(a, followAmb, &fx, &fz); *ty = atan2f(-fx, -fz); return 1; }
    followAmb = -1;
  }
  if (followCar >= 0 && !cars[followCar].on) {
    int old = followCar; followCar = -1;
    for (int k = 0; k < 60; k++) { int c = GetRandomValue(0, NCAR - 1); if (cars[c].on && c != old) { followCar = c; break; } }
  }
  if (followCar >= 0) { float fx, fz; *cp = CarWorld(&cars[followCar], &fx, &fz, .3f); *ty = atan2f(-fx, -fz); return 1; }
  return 0;
}
static void PickFollow(void) {
  followCar = followAmb = -1;
  for (int k = 0; k < NAMB; k++) if (amb[k].st == 1 || amb[k].st == 3) { followAmb = k; return; }
  for (int k = 0; k < 80; k++) { int c = GetRandomValue(0, NCAR - 1); if (cars[c].on) { followCar = c; return; } }
}
static void UpdateCam3D(float dt) {
  Vector3 cp; float ty, tm = (float)GetTime();
  if (camPreset == 3) {
    if (!FollowPt(&cp, &ty)) PickFollow();
    if (FollowPt(&cp, &ty)) {
      float dy = ty - camYaw;
      while (dy > PI) dy -= 2 * PI;
      while (dy < -PI) dy += 2 * PI;
      camT = Vector3Lerp(camT, cp, fminf(1, 8 * dt)); camYaw += dy * fminf(1, 1.8f * dt); camPitch = Appr(camPitch, .42f, 2, dt); camDist = Appr(camDist, followDist, 4, dt);
    }
    return;
  }
  if (camPreset == 1) { camPitch = Appr(camPitch, 1.45f, 3, dt); camYaw = Appr(camYaw, 0, 3, dt); camT = Vector3Lerp(camT, (Vector3){0, 0, 0}, fminf(1, 3 * dt)); }
  else if (camPreset == 2) {
    camYaw += .12f * dt; camPitch = Appr(camPitch, .5f + .12f * sinf(tm * .2f), 2, dt);
    camT = Vector3Lerp(camT, (Vector3){8 * sinf(tm * .07f), 0, 5 * cosf(tm * .05f)}, fminf(1, .8f * dt)); userDist = Appr(userDist, 58 + 12 * sinf(tm * .1f), 1, dt);
  }
  camDist = Appr(camDist, userDist, 6, dt);
}

static int Pick3D(Vector2 mp, Vector2 *out, int *bhit) { /* ray from the mouse: ground point, plus building boxes */
  Rectangle dst = {R_MAP.x + 8, R_MAP.y + 44, R_MAP.width - 16, R_MAP.height - 52}; float best = 1e9f;
  *bhit = -1;
  if (!CheckCollisionPointRec(mp, dst)) return 0;
  ray3 = GetScreenToWorldRayEx((Vector2){(mp.x - dst.x) / dst.width * rt3.texture.width, (mp.y - dst.y) / dst.height * rt3.texture.height}, cam3, rt3.texture.width, rt3.texture.height);
  for (int b = 0; b < nBld; b++) {
    Bld *q = &bld[b]; Vector3 c = W3(q->x, q->y, 0); float r = .5f * hypotf(q->w, q->d) / 10 * .85f, hh = q->h + (q->type == BT_HOME ? 1.0f : .3f);
    RayCollision rc = GetRayCollisionBox(ray3, (BoundingBox){{c.x - r, 0, c.z - r}, {c.x + r, hh, c.z + r}});
    if (rc.hit && rc.distance < best) { best = rc.distance; *bhit = b; }
  }
  if (ray3.direction.y > -1e-4f) return 0;
  { float t = -ray3.position.y / ray3.direction.y; Vector3 h = Vector3Add(ray3.position, Vector3Scale(ray3.direction, t)); *out = (Vector2){h.x * 10 + cx3, h.z * 10 + cy3}; }
  return 1;
}

static void Render3D(void) {
  float elev = sinf((fmodf(clockS / 3600, 24) - 6) / 12 * PI), an = (fmodf(clockS / 3600, 24) - 6) / 12 * PI;
  float t = (float)GetTime(), pulse = .5f + .5f * sinf(t * 4), dtf = GetFrameTime(), cp = cosf(camPitch);
  float sd = Clamp(1 - fabsf(elev - .1f) / .22f, 0, 1), nf = Clamp(1 - elev * 3.0f, 0, 1), lit = Clamp(elev * 3.0f + .25f, 0, 1);
  Vector3 S = elev > .05f ? Vector3Normalize((Vector3){-cosf(an), elev, .35f}) : Vector3Normalize((Vector3){.3f, .7f, -.4f});
  Vector3 warm = {1.0f, .62f, .38f}, white = {1.0f, .95f, .86f}, moon = {.20f, .25f, .42f};
  Vector3 sunC = elev > .05f ? Vector3Scale(Vector3Lerp(warm, white, Clamp(elev * 2.2f, 0, 1)), .35f + .75f * elev) : moon;
  Vector3 ambc = Vector3Add(Vector3Lerp((Vector3){.17f, .20f, .32f}, (Vector3){.40f, .44f, .54f}, lit), Vector3Scale((Vector3){.12f, .05f, 0}, sd));
  Color sky = Mix(Mix((Color){9, 12, 28, 255}, (Color){112, 166, 222, 255}, Clamp(elev * 2.5f + .1f, 0, 1)), (Color){236, 132, 92, 255}, sd * .75f);
  Color grass = Mix((Color){26, 44, 36, 255}, (Color){52, 104, 66, 255}, lit), water = Mix((Color){18, 40, 80, 255}, (Color){52, 118, 186, 255}, lit);
  float pl[12][4] = {{0}}, plc[12][3] = {{0}}, fogDen; int np = 0, usedL[4] = {-1, -1, -1, -1}; Vector2 sh = {0, 0}; int shadows = quality && elev > .08f;
  Color shk = {0, 0, 0, (unsigned char)(55 * Clamp(elev * 2, 0, 1))}; Vector3 cpos;
  if (rain) { sky = Mix(sky, (Color){80, 88, 104, 255}, .5f); sunC = Vector3Scale(sunC, .6f); }
  sky = Mix(sky, (Color){178, 184, 196, 255}, fogL * .85f);
  fogDen = .0035f + .0095f * fogL + (rain ? .0025f : 0);
  cam3.position = (Vector3){camT.x + camDist * cp * sinf(camYaw), camT.y + camDist * sinf(camPitch), camT.z + camDist * cp * cosf(camYaw)};
  cam3.target = camT; cam3.up = (Vector3){0, 1, 0}; cam3.fovy = 45; cam3.projection = CAMERA_PERSPECTIVE; cpos = cam3.position;
  if (shadows) { sh = (Vector2){-S.x / S.y, -S.z / S.y}; { float l = Vector2Length(sh); if (l > 3) sh = Vector2Scale(sh, 3 / l); } }
  /* dynamic point lights: sirens, crash beacons, nearby lamps, headlights */
  for (int k = 0; k < NAMB; k++) if (amb[k].st) { float fx, fz; Vector3 p = AmbWorld(&amb[k], k, &fx, &fz); int f = sinf(t * 14 + k) > 0; p.y = 1; AddPL(pl, plc, &np, p, 10, f ? 1.6f : .2f, .2f, f ? .2f : 1.6f); }
  for (int e = 0; e < nE; e += 2) if (E[e].crash > 0 || E[e + 1].crash > 0) { Vector3 p = W3((N[E[e].a].x + N[E[e].b].x) / 2, (N[E[e].a].y + N[E[e].b].y) / 2, 1.2f); int f = sinf(t * 12) > 0; AddPL(pl, plc, &np, p, 8, f ? 1.5f : .2f, .2f, f ? .2f : 1.5f); }
  if (nf > .3f) for (int q = 0; q < 4; q++) {
    int best = -1; float bd = 1e9f;
    for (int i = 0; i < nLamp; i++) {
      Vector3 w = W3(lamps[i].x, lamps[i].y, 0); float dd = (w.x - camT.x) * (w.x - camT.x) + (w.z - camT.z) * (w.z - camT.z); int used = 0;
      for (int u = 0; u < q; u++) if (usedL[u] == i) used = 1;
      if (!used && dd < bd) { bd = dd; best = i; }
    }
    if (best >= 0) { usedL[q] = best; AddPL(pl, plc, &np, W3(lamps[best].x, lamps[best].y, 2.2f), 9, nf, .72f * nf, .38f * nf); }
  }
  { Vector3 dsun = Vector3Negate(S), cc = {(float)sky.r / 255, (float)sky.g / 255, (float)sky.b / 255};
    SetShaderValue(sh3, lSun, &dsun, SHADER_UNIFORM_VEC3); SetShaderValue(sh3, lSunC, &sunC, SHADER_UNIFORM_VEC3); SetShaderValue(sh3, lAmb, &ambc, SHADER_UNIFORM_VEC3);
    SetShaderValue(sh3, lCam, &cpos, SHADER_UNIFORM_VEC3); SetShaderValue(sh3, lFogC, &cc, SHADER_UNIFORM_VEC3); SetShaderValue(sh3, lFogD, &fogDen, SHADER_UNIFORM_FLOAT);
    SetShaderValueV(sh3, lPl, pl, SHADER_UNIFORM_VEC4, 12); SetShaderValueV(sh3, lPlc, plc, SHADER_UNIFORM_VEC3, 12); }

  BeginTextureMode(rt3); ClearBackground(sky); BeginMode3D(cam3); rlDisableBackfaceCulling();
  DrawSphere(Vector3Add(camT, Vector3Scale(S, 220)), elev > .05f ? 10 : 6, Mix(elev > .05f ? (Color){255, 236, 180, 255} : (Color){220, 228, 255, 255}, sky, fogL));
  BeginShaderMode(sh3);
  DrawCubeV((Vector3){0, -.1f, 0}, (Vector3){190, .2f, 150}, grass);
  RectQ(OX + 315, OY + 28, OX + 440, OY + 136, .02f, Mix(grass, (Color){80, 160, 90, 255}, .35f));
  RectQ(OX + 440, OY + 250, OX + 640, OY + 440, .02f, (Color){92, 96, 110, 255});
  RectQ(OX + 503, OY + 150, OX + 590, OY + 205, .07f, (Color){160, 154, 144, 255});
  for (int i = 0; i < 7; i++) {
    Vector3 a = W3(OX + RV[i][0], OY + RV[i][1], 0), b = W3(OX + RV[i + 1][0], OY + RV[i + 1][1], 0);
    Ribbon(a.x, a.z, b.x, b.z, 3.8f, .03f, water); DrawCylinder((Vector3){b.x, 0, b.z}, 1.9f, 1.9f, .03f, 14, water);
  }
  DrawCylinder(W3(OX + 380, OY + 70, 0), 2.8f, 2.8f, .035f, 24, water);
  for (int e = 0; e < nE; e += 2) { /* sidewalks, then roads on top */
    Vector3 a = W3(N[E[e].a].x, N[E[e].a].y, 0), b = W3(N[E[e].b].x, N[E[e].b].y, 0);
    Ribbon(a.x, a.z, b.x, b.z, RW(E[e].cls) / 10 + 1.0f, .06f, E[e].bridge ? (Color){130, 134, 150, 255} : (Color){138, 142, 158, 255});
  }
  for (int n = 0; n < NNODE; n++) { Vector3 p = W3(N[n].x, N[n].y, 0); DrawCylinder((Vector3){p.x, .0005f, p.z}, RW(N[n].maxcls) / 20 + .5f, RW(N[n].maxcls) / 20 + .5f, .06f, 14, (Color){138, 142, 158, 255}); }
  for (int e = 0; e < nE; e += 2) {
    Vector3 a = W3(N[E[e].a].x, N[E[e].a].y, 0), b = W3(N[E[e].b].x, N[E[e].b].y, 0); int cl = E[e].cls;
    Color rc = E[e].bridge ? (Color){92, 96, 114, 255} : cl >= 2 ? (Color){54, 58, 76, 255} : (Color){46, 50, 66, 255};
    if (E[e].closed) rc = Mix(rc, C_RED, .35f);
    Ribbon(a.x, a.z, b.x, b.z, RW(cl) / 10, .10f, rc);
  }
  for (int n = 0; n < NNODE; n++) { Vector3 p = W3(N[n].x, N[n].y, 0); int cl = N[n].maxcls; DrawCylinder((Vector3){p.x, .0005f, p.z}, RW(cl) / 20, RW(cl) / 20, .1f, 14, cl >= 2 ? (Color){54, 58, 76, 255} : (Color){46, 50, 66, 255}); }
  for (int e = 0; e < nE; e += 2) if (E[e].bridge) { /* bridge parapets */
    Vector3 a = W3(N[E[e].a].x, N[E[e].a].y, 0), b = W3(N[E[e].b].x, N[E[e].b].y, 0), m = Vector3Lerp(a, b, .5f); float w = RW(E[e].cls) / 20 + .15f;
    OBox((Vector3){m.x - E[e].uy * w, .32f, m.z + E[e].ux * w}, E[e].ux, E[e].uy, E[e].len / 10, .45f, .16f, (Color){190, 194, 208, 255});
    OBox((Vector3){m.x + E[e].uy * w, .32f, m.z - E[e].ux * w}, E[e].ux, E[e].uy, E[e].len / 10, .45f, .16f, (Color){190, 194, 208, 255});
  }
  for (int e = 0; e < nE; e += 2) if (E[e].cls >= 1 && !E[e].bridge) { /* dashed centre lines */
    Vector3 a = W3(N[E[e].a].x, N[E[e].a].y, 0); float L = E[e].len / 10, ux = E[e].ux, uz = E[e].uy; Color mk = E[e].cls >= 2 ? (Color){236, 206, 110, 255} : (Color){200, 204, 214, 255};
    for (float d = 1.6f; d + .6f < L - 1.6f; d += 1.2f) Ribbon(a.x + ux * d, a.z + uz * d, a.x + ux * (d + .6f), a.z + uz * (d + .6f), .09f, .115f, mk);
  }
  for (int n = 0; n < NNODE; n++) if (N[n].sig) for (int e = 0; e < nE; e++) if (E[e].b == n) { /* zebra crossings */
    Vector3 c = W3(N[n].x - E[e].ux * 13, N[n].y - E[e].uy * 13, 0); float w = RW(E[e].cls) / 10, nx = -E[e].uy, nz = E[e].ux;
    for (int k = 0; k < 5; k++) { float off = -w / 2 + (k + .5f) * w / 5, px = c.x + nx * off, pz = c.z + nz * off; Ribbon(px - E[e].ux * .5f, pz - E[e].uy * .5f, px + E[e].ux * .5f, pz + E[e].uy * .5f, .28f, .122f, (Color){210, 214, 224, 255}); }
  }
  for (int e = 0; e < nE; e++) { /* live congestion colour strips */
    float rt = E[e].ratio, off = RW(E[e].cls) / 10 * .26f; Vector3 a = W3(N[E[e].a].x, N[E[e].a].y, 0); float L = E[e].len / 10;
    Color cc = rt > .6f ? Mix(C_AMBER, C_GREEN, (rt - .6f) / .4f) : Mix(C_RED, C_AMBER, rt / .6f); float nx = -E[e].uy * off, nz = E[e].ux * off;
    if (E[e].closed) cc = (Color){70, 76, 100, 255};
    Ribbon(a.x + E[e].ux * 1.3f + nx, a.z + E[e].uy * 1.3f + nz, a.x + E[e].ux * (L - 1.3f) + nx, a.z + E[e].uy * (L - 1.3f) + nz, .12f, .13f, cc);
  }
  { float x = (OX + 235 - cx3) / 10, z0 = (OY + 110 - cy3) / 10, z1 = (OY + 395 - cy3) / 10; /* railway */
    Ribbon(x - .32f, z0, x - .32f, z1, .1f, .11f, (Color){160, 166, 180, 255}); Ribbon(x + .32f, z0, x + .32f, z1, .1f, .11f, (Color){160, 166, 180, 255});
    for (float z = z0 + .3f; z < z1; z += .7f) Ribbon(x - .7f, z, x + .7f, z, .2f, .105f, (Color){70, 56, 46, 255});
  }
  if (shadows) { /* planar sun shadows */
    for (int b = 0; b < nBld; b++) { Bld *q = &bld[b]; Vector3 c = W3(q->x, q->y, 0); ShadowBox(c.x, c.z, q->fx, q->fy, q->w / 10, q->d / 10, q->h + (q->type == BT_HOME ? .9f : 0), sh, shk); }
    for (int i = 0; i < nTree; i++) { Vector3 c = W3(trees[i].x, trees[i].y, 0); ShadowBox(c.x, c.z, 1, 0, .9f, .9f, 1.8f * trees[i].z, sh, shk); }
  }
  for (int b = 0; b < nBld; b++) { /* buildings */
    static const Color HW[5] = {{214, 196, 170, 255}, {190, 170, 160, 255}, {200, 205, 185, 255}, {176, 186, 206, 255}, {222, 206, 160, 255}};
    static const Color HR[5] = {{150, 70, 56, 255}, {96, 100, 118, 255}, {120, 64, 60, 255}, {82, 92, 100, 255}, {140, 90, 54, 255}};
    static const Color SW_[5] = {{230, 130, 110, 255}, {120, 180, 220, 255}, {240, 200, 100, 255}, {150, 200, 140, 255}, {200, 140, 210, 255}};
    Bld *q = &bld[b]; Vector3 c = W3(q->x, q->y, 0); float L = q->w / 10, W = q->d / 10, H = q->h, fx = q->fx, fz = q->fy;
    switch (q->type) {
      case BT_HOME:
        OBox((Vector3){c.x, H / 2, c.z}, fx, fz, L, H, W, HW[q->col]); RoofP((Vector3){c.x, H, c.z}, fx, fz, L * 1.12f, W * 1.2f, .95f, HR[q->col]);
        OBox((Vector3){c.x + fx * L * .25f, H + .75f, c.z + fz * L * .25f}, fx, fz, .22f, .7f, .22f, (Color){120, 90, 80, 255}); break;
      case BT_SHOP:
        OBox((Vector3){c.x, H / 2, c.z}, fx, fz, L, H, W, SW_[q->col]); OBox((Vector3){c.x, H + .06f, c.z}, fx, fz, L * 1.04f, .12f, W * 1.04f, (Color){90, 94, 110, 255});
        OBox((Vector3){c.x - fz * (W / 2 + .2f), H * .62f, c.z + fx * (W / 2 + .2f)}, fx, fz, L * .92f, .08f, .55f, SW_[(q->col + 2) % 5]); break;
      case BT_OFFICE:
        OBox((Vector3){c.x, H / 2, c.z}, fx, fz, L, H, W, (Color){90 + q->col * 8, 112 + q->col * 6, 156, 255}); OBox((Vector3){c.x, H + .08f, c.z}, fx, fz, L * 1.04f, .16f, W * 1.04f, (Color){60, 66, 86, 255});
        DrawCylinder((Vector3){c.x, H, c.z}, .04f, .06f, 1.1f, 5, (Color){180, 184, 196, 255}); break;
      case BT_SCHOOL:
        OBox((Vector3){c.x, H / 2, c.z}, fx, fz, L, H, W, (Color){214, 190, 120, 255}); RoofP((Vector3){c.x, H, c.z}, fx, fz, L * 1.08f, W * 1.1f, .6f, (Color){150, 70, 56, 255});
        DrawCylinder((Vector3){c.x + fx * L * .7f - fz * W * .9f, 0, c.z + fz * L * .7f + fx * W * .9f}, .03f, .03f, 3, 5, (Color){200, 200, 210, 255}); break;
      case BT_IND:
        OBox((Vector3){c.x, H / 2, c.z}, fx, fz, L, H, W, (Color){136, 140, 154, 255}); RoofP((Vector3){c.x, H, c.z}, fx, fz, L, W * 1.02f, .35f, (Color){96, 100, 114, 255});
        DrawCylinder((Vector3){c.x + fx * L * .3f, H, c.z + fz * L * .3f}, .22f, .3f, 1.9f, 8, (Color){90, 80, 76, 255}); DrawCylinder((Vector3){c.x - fx * L * .3f - fz * W * .6f, 0, c.z - fz * L * .3f + fx * W * .6f}, .5f, .5f, 1.5f, 10, (Color){200, 204, 214, 255}); break;
      case BT_STAD:
        DrawCylinder((Vector3){c.x, 0, c.z}, L * .5f, L * .56f, 1.8f, 28, Mix(C_VIOLET, C_BG, .35f)); DrawCylinder((Vector3){c.x, 0, c.z}, L * .38f, L * .38f, 1.86f, 28, (Color){18, 14, 36, 255});
        DrawCylinder((Vector3){c.x, 0, c.z}, L * .34f, L * .34f, 1.9f, 28, (Color){28, 84, 60, 255});
        for (int k = 0; k < 4; k++) { float dx = (k % 2 ? 1 : -1) * L * .46f, dz = (k / 2 ? 1 : -1) * L * .46f; DrawCylinder((Vector3){c.x + dx, 0, c.z + dz}, .09f, .12f, 4.8f, 6, (Color){120, 126, 146, 255}); } break;
      case BT_HOSP:
        OBox((Vector3){c.x, H / 2, c.z}, fx, fz, L, H, W, (Color){228, 234, 246, 255}); OBox((Vector3){c.x, H + .05f, c.z}, fx, fz, L * 1.04f, .1f, W * 1.04f, (Color){190, 200, 225, 255});
        OBox((Vector3){c.x, H + .12f, c.z}, fx, fz, 1.6f, .06f, .45f, C_RED); OBox((Vector3){c.x, H + .12f, c.z}, fx, fz, .45f, .06f, 1.6f, C_RED); break;
      case BT_MARKET:
        for (int k = 0; k < 6; k++) {
          float s = (k - 2.5f) * L / 6.2f; Vector3 p = {c.x + fx * s, .45f, c.z + fz * s};
          OBox(p, fx, fz, L / 7, .9f, W * .7f, (Color){150, 110, 80, 255}); OBox((Vector3){p.x, 1.0f, p.z}, fx, fz, L / 6.6f, .08f, W * .95f, k % 2 ? C_PINK : C_AMBER);
        } break;
      case BT_MILL:
        DrawCylinder((Vector3){c.x, 0, c.z}, .5f, .95f, 3.2f, 8, (Color){214, 200, 170, 255}); DrawCylinder((Vector3){c.x, 3.2f, c.z}, 0, .65f, .9f, 8, (Color){120, 70, 56, 255});
        for (int k = 0; k < 4; k++) { float a = t * .8f + k * PI / 2; DrawCylinderEx((Vector3){c.x, 3.0f, c.z + .75f}, (Vector3){c.x + cosf(a) * 2.0f, 3.0f + sinf(a) * 2.0f, c.z + .75f}, .05f, .05f, 4, (Color){110, 80, 60, 255}); } break;
      case BT_FOUNT: {
        DrawCylinder((Vector3){c.x, .06f, c.z}, 1.5f, 1.5f, .35f, 16, (Color){170, 166, 160, 255}); DrawCylinder((Vector3){c.x, .06f, c.z}, 1.3f, 1.3f, .38f, 16, water);
        DrawCylinder((Vector3){c.x, .06f, c.z}, .12f, .16f, 1.1f, 6, (Color){180, 176, 170, 255});
        for (int k = 0; k < 8; k++) { float ph = fmodf(t * .9f + k * .125f, 1), a = k * PI / 4, r = 1.1f * ph; DrawSphereEx((Vector3){c.x + cosf(a) * r, 1.1f + 1.2f * ph * (1 - ph) * 2, c.z + sinf(a) * r}, .07f, 3, 4, (Color){200, 228, 255, 255}); }
      } break;
      default: OBox((Vector3){c.x, H / 2, c.z}, fx, fz, L, H, W, (Color){150, 150, 170, 255}); OBox((Vector3){c.x, .1f, c.z}, fx, fz, L * 1.3f, .2f, W * 1.6f, (Color){110, 112, 126, 255}); break;
    }
  }
  for (int i = 0; i < nTree; i++) { /* trees */
    Vector3 c = W3(trees[i].x, trees[i].y, 0); float s = trees[i].z;
    DrawCylinder(c, .07f * s, .11f * s, .75f * s, 5, (Color){92, 64, 44, 255});
    if (i % 3) DrawSphereEx((Vector3){c.x, 1.25f * s, c.z}, .62f * s, 4, 5, Mix((Color){36, 96, 52, 255}, (Color){86, 150, 70, 255}, (float)(i % 7) / 7));
    else DrawCylinder((Vector3){c.x, .55f * s, c.z}, 0, .55f * s, 1.7f * s, 6, (Color){30, 80, 56, 255});
  }
  for (int i = 0; i < nLamp; i++) { Vector3 p = W3(lamps[i].x, lamps[i].y, 0); DrawCylinder(p, .035f, .05f, 2.35f, 5, (Color){72, 76, 92, 255}); }
  for (int n = 0; n < NNODE; n++) if (N[n].sig) for (int e = 0; e < nE; e++) if (E[e].b == n) { /* signal poles */
    Vector3 p = W3(N[n].x - E[e].ux * 11 - E[e].uy * (RW(E[e].cls) / 2 + 6), N[n].y - E[e].uy * 11 + E[e].ux * (RW(E[e].cls) / 2 + 6), 0);
    DrawCylinder(p, .035f, .05f, 1.6f, 5, (Color){70, 74, 90, 255}); OBox((Vector3){p.x, 1.75f, p.z}, 1, 0, .26f, .62f, .26f, (Color){30, 32, 42, 255});
  }
  for (int i = 0; i < NCAR; i++) if (cars[i].on) { /* cars with wheels */
    static const Color CC[8] = {{210, 60, 70, 255}, {60, 110, 200, 255}, {230, 230, 236, 255}, {40, 44, 54, 255}, {230, 180, 60, 255}, {70, 160, 110, 255}, {150, 154, 164, 255}, {190, 90, 200, 255}};
    float fx, fz, L = cars[i].type == 2 ? 1.9f : cars[i].type == 1 ? 1.25f : .95f, Wd = cars[i].type == 2 ? .62f : .48f, Hb = cars[i].type == 2 ? .5f : .22f, Hc = cars[i].type == 2 ? .26f : .2f;
    Vector3 p = CarWorld(&cars[i], &fx, &fz, .12f); Color body = cars[i].div > 0 ? Mix(C_VIOLET, WHITE, .2f) : cars[i].type == 2 ? (Color){230, 200, 60, 255} : CC[i % 8];
    OBox((Vector3){p.x, p.y + Hb / 2, p.z}, fx, fz, L, Hb, Wd, body);
    OBox((Vector3){p.x - fx * L * .05f, p.y + Hb + Hc / 2, p.z - fz * L * .05f}, fx, fz, L * (cars[i].type == 2 ? .92f : .5f), Hc, Wd * .84f, (Color){34, 46, 70, 255});
    if (Vector3Distance(p, cpos) < 36) for (int w = 0; w < 4; w++) {
      float sf = (w & 1) ? 1 : -1, sr = (w & 2) ? 1 : -1, ax = -fz, az = fx; Vector3 wc = {p.x + fx * sf * L * .32f + ax * sr * Wd * .5f, .13f, p.z + fz * sf * L * .32f + az * sr * Wd * .5f};
      DrawCylinderEx((Vector3){wc.x - ax * .05f, wc.y, wc.z - az * .05f}, (Vector3){wc.x + ax * .05f, wc.y, wc.z + az * .05f}, .13f, .13f, 7, (Color){20, 22, 28, 255});
    }
  }
  for (int k = 0; k < NAMB; k++) { /* ambulances */
    float fx, fz; Vector3 p = AmbWorld(&amb[k], k, &fx, &fz);
    OBox((Vector3){p.x, .5f, p.z}, fx, fz, 1.3f, .55f, .58f, (Color){240, 244, 250, 255}); OBox((Vector3){p.x, .5f, p.z}, fx, fz, 1.32f, .12f, .6f, C_RED);
    OBox((Vector3){p.x + fx * .3f, .85f, p.z + fz * .3f}, fx, fz, .4f, .2f, .5f, (Color){34, 46, 70, 255});
    if (k == followAmb) DrawCubeWiresV((Vector3){p.x, .55f, p.z}, (Vector3){1.7f, .9f, 1.0f}, WHITE);
  }
  for (int i = 0; i < nPed; i++) { /* pedestrians on the crossings */
    Vector2 q = PedPos(&ped[i]); Vector3 p = W3(q.x, q.y, 0); int mv = ped[i].t > .01f && ped[i].t < .99f; float bob = mv ? fabsf(sinf(t * 8 + i)) * .04f : 0;
    DrawCubeV((Vector3){p.x, .3f + bob, p.z}, (Vector3){.13f, .42f, .12f}, ped[i].c); DrawSphereEx((Vector3){p.x, .62f + bob, p.z}, .07f, 3, 4, (Color){226, 190, 160, 255});
  }
  for (int i = 0; i < (marketT > 0 ? 14 : 6); i++) { /* plaza and park strollers */
    Vector2 d = {strollT[i].x - strollP[i].x, strollT[i].y - strollP[i].z}; float l = Vector2Length(d);
    if (l < .15f) { if (i < 8) strollT[i] = (Vector2){W3(OX + 545 + (rnd() - .5f) * 74, 0, 0).x, (OY + 177 + (rnd() - .5f) * 44 - cy3) / 10}; else strollT[i] = (Vector2){(OX + 330 + rnd() * 100 - cx3) / 10, (OY + 100 + rnd() * 30 - cy3) / 10}; }
    else { strollP[i].x += d.x / l * .8f * dtf; strollP[i].z += d.y / l * .8f * dtf; }
    DrawCubeV((Vector3){strollP[i].x, .3f, strollP[i].z}, (Vector3){.13f, .42f, .12f}, (Color){(unsigned char)(60 + i * 12), (unsigned char)(90 + i * 7), (unsigned char)(200 - i * 9), 255});
    DrawSphereEx((Vector3){strollP[i].x, .62f, strollP[i].z}, .07f, 3, 4, (Color){226, 190, 160, 255});
  }
  { Vector3 c17 = W3(N[17].x, N[17].y, 0), tc = W3(OX + 235, trainY, 0); float a = barPos; /* train and barriers */
    for (int k = 0; k < 4; k++) OBox((Vector3){tc.x, .55f, tc.z + trainDir * (1.5f - k * 2.9f)}, 0, 1, 2.6f, 1.0f, 1.1f, k == 0 ? (Color){190, 50, 56, 255} : (Color){110, 126, 160, 255});
    for (int s = 0; s < 2; s++) {
      float sg = s ? 1 : -1; Vector3 post = {c17.x - sg * 2.6f, 0, c17.z - sg * 1.6f}, top = {post.x, 1.1f, post.z};
      Vector3 tip = {post.x, 1.1f + 1.7f * cosf(a * PI / 2), post.z + sg * 1.7f * sinf(a * PI / 2)}, mid = Vector3Lerp(top, tip, .5f);
      DrawCylinder(post, .06f, .08f, 1.1f, 6, (Color){200, 200, 210, 255});
      DrawCylinderEx(top, mid, .05f, .05f, 5, WHITE); DrawCylinderEx(mid, tip, .05f, .05f, 5, C_RED);
    }
  }
  EndShaderMode();

  /* ----- unlit pass: windows, lamps, signals, vehicle lights ----- */
  if (quality) for (int b = 0; b < nBld; b++) {
    Bld *q = &bld[b]; Vector3 c = W3(q->x, q->y, 0); float L = q->w / 10, W = q->d / 10, H = q->h, fx = q->fx, fz = q->fy, sp = q->type == BT_OFFICE ? .9f : q->type == BT_IND ? 2.0f : 1.2f;
    if (Vector3Distance(c, cpos) > 85 || q->type > BT_HOSP || q->type == BT_STAD) continue;
    WinFace((Vector3){c.x + fx * L / 2, 0, c.z + fz * L / 2}, fx, fz, W, H, q->type == BT_OFFICE ? .6f : .55f, (unsigned)b, nf, sp);
    WinFace((Vector3){c.x - fx * L / 2, 0, c.z - fz * L / 2}, -fx, -fz, W, H, q->type == BT_OFFICE ? .6f : .55f, (unsigned)b + 7, nf, sp);
    WinFace((Vector3){c.x - fz * W / 2, 0, c.z + fx * W / 2}, -fz, fx, L, H, q->type == BT_OFFICE ? .6f : .55f, (unsigned)b + 13, nf, sp);
    WinFace((Vector3){c.x + fz * W / 2, 0, c.z - fx * W / 2}, fz, -fx, L, H, q->type == BT_OFFICE ? .6f : .55f, (unsigned)b + 19, nf, sp);
  }
  for (int i = 0; i < nLamp; i++) { Vector3 p = W3(lamps[i].x, lamps[i].y, 2.38f); DrawCubeV(p, (Vector3){.22f, .1f, .22f}, nf > .3f ? (Color){255, 214, 140, 255} : (Color){150, 154, 166, 255}); }
  for (int n = 0; n < NNODE; n++) if (N[n].sig) for (int e = 0; e < nE; e++) if (E[e].b == n) { /* signal lamps */
    int s = Sig(n, E[e].horiz), blink = (int)(t * 2) % 2; Vector3 p = W3(N[n].x - E[e].ux * 11 - E[e].uy * (RW(E[e].cls) / 2 + 6), N[n].y - E[e].uy * 11 + E[e].ux * (RW(E[e].cls) / 2 + 6), 1.75f);
    DrawCubeV((Vector3){p.x, p.y + .2f, p.z}, (Vector3){.14f, .14f, .14f}, s == 0 ? C_RED : (Color){70, 20, 26, 255});
    DrawCubeV(p, (Vector3){.14f, .14f, .14f}, (s == 2 || (s == 4 && blink)) ? C_AMBER : (Color){70, 56, 24, 255});
    DrawCubeV((Vector3){p.x, p.y - .2f, p.z}, (Vector3){.14f, .14f, .14f}, s == 1 ? C_GREEN : (Color){20, 60, 40, 255});
  }
  for (int i = 0; i < NCAR; i++) if (cars[i].on) {
    float fx, fz, L = cars[i].type == 2 ? 1.9f : cars[i].type == 1 ? 1.25f : .95f, Wd = cars[i].type == 2 ? .62f : .48f; Vector3 p = CarWorld(&cars[i], &fx, &fz, .3f);
    if (Vector3Distance(p, cpos) > 40) continue;
    for (int s = -1; s <= 1; s += 2) {
      float ax = -fz * s * Wd * .36f, az = fx * s * Wd * .36f;
      if (nf > .3f || rain || fogL > .3f) DrawCubeV((Vector3){p.x + fx * L * .5f + ax, p.y - .06f, p.z + fz * L * .5f + az}, (Vector3){.08f, .07f, .08f}, (Color){255, 246, 210, 255});
      DrawCubeV((Vector3){p.x - fx * L * .5f + ax, p.y - .06f, p.z - fz * L * .5f + az}, (Vector3){.08f, .07f, .08f}, cars[i].br > 0 ? (Color){255, 40, 40, 255} : (Color){110, 20, 24, 255});
    }
  }
  for (int k = 0; k < NAMB; k++) { float fx, fz; Vector3 p = AmbWorld(&amb[k], k, &fx, &fz); int f = sinf(t * 14 + k) > 0; DrawCubeV((Vector3){p.x, 1.0f, p.z}, (Vector3){.35f, .14f, .35f}, f ? C_RED : C_CYAN); }
  for (int e = 0; e < nE; e += 2) if (E[e].crash > 0 || E[e + 1].crash > 0) {
    Vector3 m = W3((N[E[e].a].x + N[E[e].b].x) / 2, (N[E[e].a].y + N[E[e].b].y) / 2, 0); int f = sinf(t * 12) > 0;
    DrawCubeV((Vector3){m.x, .45f, m.z}, (Vector3){.7f, .9f, .5f}, (Color){60, 64, 84, 255}); DrawSphere((Vector3){m.x, 1.3f, m.z}, .35f, f ? C_RED : C_CYAN);
  }
  for (int e = 0; e < nE; e += 2) {
    Vector3 a = W3(N[E[e].a].x, N[E[e].a].y, 0), m = Vector3Lerp(a, W3(N[E[e].b].x, N[E[e].b].y, 0), .5f); float L = E[e].len / 10;
    if (E[e].works > 0) for (int k = 0; k < 6; k++) {
      float d = 2.6f + k * (L - 5.2f) / 5; DrawCylinder((Vector3){a.x + E[e].ux * d, .1f, a.z + E[e].uy * d}, 0, .24f, .6f, 8, (Color){255, 120, 30, 255});
      DrawCylinder((Vector3){a.x + E[e].ux * d, .3f, a.z + E[e].uy * d}, .14f, .17f, .08f, 8, WHITE);
    }
    if (E[e].closed) OBox((Vector3){m.x, .5f, m.z}, E[e].ux, E[e].uy, .25f, 1.0f, RW(E[e].cls) / 10 * 1.1f, C_RED);
  }
  if (barrierDown) for (int s = 0; s < 2; s++) { float sg = s ? 1 : -1; Vector3 c17 = W3(N[17].x, N[17].y, 0); DrawSphere((Vector3){c17.x - sg * 2.6f, 1.3f, c17.z - sg * 1.6f}, .13f, ((int)(t * 3) + s) % 2 ? C_RED : (Color){80, 10, 14, 255}); }

  /* ----- glow: additive halos ----- */
  if (quality) {
    float gf = 1 - fogL * .7f; BeginBlendMode(BLEND_ADDITIVE); rlDisableDepthMask();
    for (int i = 0; i < nLamp; i++) { Vector3 p = W3(lamps[i].x, lamps[i].y, 2.35f); float gs = Clamp(Vector3Distance(p, cpos) / 45.0f, .3f, 1.0f); if (nf > .3f && Vector3Distance(p, cpos) < 80) { DrawSphere(p, .45f * gs, Fade((Color){255, 190, 100, 255}, .22f * nf * gf)); DrawSphere(p, .95f * gs, Fade((Color){255, 190, 100, 255}, .07f * nf * gf)); } }
    for (int n = 0; n < NNODE; n++) if (N[n].sig) for (int e = 0; e < nE; e++) if (E[e].b == n) {
      int s = Sig(n, E[e].horiz); Vector3 p = W3(N[n].x - E[e].ux * 11 - E[e].uy * (RW(E[e].cls) / 2 + 6), N[n].y - E[e].uy * 11 + E[e].ux * (RW(E[e].cls) / 2 + 6), 1.75f);
      if (Vector3Distance(p, cpos) > 70) continue;
      { float gs = Clamp(Vector3Distance(p, cpos) / 40.0f, .4f, 1.0f) * .3f;
      if (s == 0) DrawSphere((Vector3){p.x, p.y + .2f, p.z}, gs, Fade(C_RED, .35f * gf)); else if (s == 1) DrawSphere((Vector3){p.x, p.y - .2f, p.z}, gs, Fade(C_GREEN, .35f * gf));
      else if (s == 2 || (s == 4 && (int)(t * 2) % 2)) DrawSphere(p, gs, Fade(C_AMBER, .35f * gf)); }
    }
    for (int i = 0; i < NCAR; i++) if (cars[i].on && (nf > .3f || rain || fogL > .3f)) {
      float fx, fz; Vector3 p = CarWorld(&cars[i], &fx, &fz, .3f);
      if (Vector3Distance(p, cpos) < 32) DrawSphere((Vector3){p.x + fx * .6f, p.y - .05f, p.z + fz * .6f}, .32f, Fade((Color){255, 240, 190, 255}, .2f * gf));
    }
    for (int k = 0; k < NAMB; k++) if (amb[k].st) { float fx, fz; Vector3 p = AmbWorld(&amb[k], k, &fx, &fz); int f = sinf(t * 14 + k) > 0; DrawSphere((Vector3){p.x, 1.0f, p.z}, 1.1f, Fade(f ? C_RED : C_CYAN, .3f)); }
    for (int e = 0; e < nE; e += 2) if (E[e].crash > 0 || E[e + 1].crash > 0) { Vector3 m = W3((N[E[e].a].x + N[E[e].b].x) / 2, (N[E[e].a].y + N[E[e].b].y) / 2, 1.3f); DrawSphere(m, 1.2f, Fade(sinf(t * 12) > 0 ? C_RED : C_CYAN, .28f)); }
    for (int i = 0; i < nBld; i++) if (bld[i].type == BT_STAD && stadiumT > 0) {
      Vector3 c = W3(bld[i].x, bld[i].y, 0); float L = bld[i].w / 10;
      for (int k = 0; k < 4; k++) DrawSphere((Vector3){c.x + (k % 2 ? 1 : -1) * L * .46f, 4.8f, c.z + (k / 2 ? 1 : -1) * L * .46f}, 1.0f + .2f * pulse, Fade(WHITE, .35f));
      DrawCylinder((Vector3){c.x, 0, c.z}, L * .3f, L * .4f, 10, 20, Fade(C_VIOLET, .08f + .06f * pulse));
    }
    for (int e = 0; e < nE; e += 2) if (E[e].works > 0) { Vector3 a = W3(N[E[e].a].x, N[E[e].a].y, 0), m = Vector3Lerp(a, W3(N[E[e].b].x, N[E[e].b].y, 0), .5f); DrawCubeV((Vector3){m.x, .13f, m.z}, E[e].horiz ? (Vector3){E[e].len / 10 - 3.5f, .02f, 1.4f} : (Vector3){1.4f, .02f, E[e].len / 10 - 3.5f}, Fade(C_AMBER, .12f + .06f * pulse)); }
    rlEnableDepthMask(); EndBlendMode();
  }
  if (rain) { /* splashes and streaks */
    for (int i = 0; i < NSPL; i++) {
      splash[i].z += dtf * 3;
      if (splash[i].z > 1) splash[i] = (Vector3){camT.x + (rnd() - .5f) * 50, camT.z + (rnd() - .5f) * 40, 0};
      if (splash[i].z < 1) DrawCircle3D((Vector3){splash[i].x, .15f, splash[i].y}, .06f + .3f * splash[i].z, (Vector3){1, 0, 0}, 90, Fade(WHITE, .5f * (1 - splash[i].z)));
    }
    for (int i = 0; i < 110; i++) {
      float ph = fmodf(t * 1.6f + i * .137f, 1); Vector3 p = {camT.x + (fmodf(i * 37.7f, 80) - 40) * .9f, 18 * (1 - ph), camT.z + (fmodf(i * 53.3f, 60) - 30) * .9f};
      DrawLine3D(p, (Vector3){p.x - .1f, p.y + .9f, p.z}, Fade(C_CYAN, .4f));
    }
  }
  EndMode3D(); EndTextureMode(); rlEnableBackfaceCulling();
}

static void DrawMap3D(void) {
  Rectangle r = R_MAP; char b[64];
  Card(r, C_BORDER); Txt("TOWN 3D", r.x + 24, r.y + 18, 12, C_MUTED, 1, AL);
  Txt("drag: orbit   shift+drag / arrows: pan   scroll: zoom   Tab: camera   F: chase   Q: quality", r.x + r.width - 24, r.y + 18, 12, C_MUTED, 0, AR);
  DrawTexturePro(rt3.texture, (Rectangle){0, 0, (float)rt3.texture.width, -(float)rt3.texture.height}, (Rectangle){r.x + 8, r.y + 44, r.width - 16, r.height - 52}, (Vector2){0, 0}, 0, WHITE);
  snprintf(b, 64, "Camera: %s", PRESET[camPreset]);
  RR((Rectangle){r.x + 20, r.y + 52, TW(b, 12, 1) + 24, 24}, 12, (Color){14, 18, 34, 215}); Txt(b, r.x + 32, r.y + 57, 12, C_TEXT, 1, AL);
}

/* ---------- main ---------- */
static void LoadFonts(void) {
  const char *reg[] = {"fonts/Inter-Regular.ttf", "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf", "/usr/share/fonts/TTF/DejaVuSans.ttf",
    "C:/Windows/Fonts/segoeui.ttf", "/System/Library/Fonts/Supplemental/Arial.ttf", "/Library/Fonts/Arial.ttf"};
  const char *bld[] = {"fonts/Inter-Bold.ttf", "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf", "/usr/share/fonts/TTF/DejaVuSans-Bold.ttf",
    "C:/Windows/Fonts/segoeuib.ttf", "/System/Library/Fonts/Supplemental/Arial Bold.ttf", "/Library/Fonts/Arial Bold.ttf"};
  fR = GetFontDefault();
  for (int i = 0; i < 6; i++) if (FileExists(reg[i])) { fR = LoadFontEx(reg[i], 48, NULL, 0); break; }
  fB = fR;
  for (int i = 0; i < 6; i++) if (FileExists(bld[i])) { fB = LoadFontEx(bld[i], 48, NULL, 0); break; }
  GenTextureMipmaps(&fR.texture); SetTextureFilter(fR.texture, TEXTURE_FILTER_TRILINEAR);
  if (fB.texture.id != fR.texture.id) { GenTextureMipmaps(&fB.texture); SetTextureFilter(fB.texture, TEXTURE_FILTER_TRILINEAR); }
}


int main(int argc, char **argv) {
  static const int MULT[3] = {1, 2, 4};
  float shotHour = -1; int shotFrames = 0, frame = 0; const char *shotFile = "shot.png"; Vector2 pressPos = {0, 0}; int pressMap = 0;
  if (argc >= 4 && strcmp(argv[1], "--shot") == 0) { view3d = atoi(argv[2]); shotFrames = atoi(argv[3]); if (argc >= 5) shotFile = argv[4]; if (argc >= 6) shotHour = (float)atof(argv[5]); SetRandomSeed(7); } /* headless test: --shot <0|1> <frames> [file] */
  SetConfigFlags(FLAG_MSAA_4X_HINT | FLAG_VSYNC_HINT);
  InitWindow(SW, SH, "Gridlock - Town Traffic Monitor"); SetTargetFPS(60); LoadFonts();
  cx3 = OX + 355; cy3 = OY + 245;
  BuildTown(); Init3D();
  for (int k = 0; k < NAMB; k++) { amb[k].hosp = k % NHOSP; amb[k].node = HN_[amb[k].hosp]; amb[k].call = -1; }
  for (int i = 0; i < NDROP; i++) drops[i] = (Vector2){R_MAP.x + rnd() * R_MAP.width, R_MAP.y + rnd() * R_MAP.height};
  for (int s = 0; s < 900; s++) SimStep(.05f); /* warm up so the town starts alive */
  delayH = co2T = 0; toastT = 0; kpiT[4] = 0; memcpy(kpiD, kpiT, sizeof kpiT); memcpy(kpiRef, kpiT, sizeof kpiT);
  AddFeed("System online: town monitoring started", C_GREEN);
  if (argc >= 7) { for (const char *k = argv[6]; *k; k++) { if (*k == 'T') ToggleAll(); else if (*k == 'C') DoCrash(); else if (*k == 'R') DoRain(); else if (*k == 'S') DoStadium(); else if (*k == 'M') DoMarket(); else if (*k == 'W') DoWorks(); else if (*k == 'O') DoFog(); } }
  if (argc >= 8) { camPreset = atoi(argv[7]); if (camPreset == 3) PickFollow(); }
  if (shotHour >= 0) { clockS = shotHour * 3600; fogL = 0; for (int s = 0; s < 400; s++) SimStep(.05f); }

  while (!WindowShouldClose()) {
    float dt = fminf(GetFrameTime(), .05f), wh = GetMouseWheelMove(); int hn = -1, he = -1, hb = -1, hov = 0; Vector2 mp = GetMousePosition(), hp = mp;
    Rectangle tgl = {R_MAP.x + 132, R_MAP.y + 10, 96, 26};
    tip.on = 0; introT += dt; toastT = fmaxf(0, toastT - dt);
    if (Hover(R_MAP) && !Hover(tgl)) {
      if (!view3d) hov = 1;
      else { int bh; if (Pick3D(mp, &hp, &bh)) hov = 1; if (hov || bh >= 0) { if (hov) PickAt(hp, &hn, &he, &hb); if (bh >= 0) { hb = bh; hn = he = -1; } hov = 1; } }
      if (!view3d) PickAt(hp, &hn, &he, &hb);
    }
    if (IsKeyPressed(KEY_P)) paused = !paused;
    if (IsKeyPressed(KEY_ONE)) speedIdx = 0;
    if (IsKeyPressed(KEY_TWO)) speedIdx = 1;
    if (IsKeyPressed(KEY_FOUR)) speedIdx = 2;
    if (IsKeyPressed(KEY_C)) { if (he >= 0) StartCrash(E[he ^ 1].cnt > E[he].cnt ? he ^ 1 : he); else DoCrash(); }
    if (IsKeyPressed(KEY_W)) { if (he >= 0) StartWorks(he); else DoWorks(); }
    if (IsKeyPressed(KEY_S)) DoStadium();
    if (IsKeyPressed(KEY_R)) DoRain();
    if (IsKeyPressed(KEY_M)) DoMarket();
    if (IsKeyPressed(KEY_O)) DoFog();
    if (IsKeyPressed(KEY_X)) ClearIncidents();
    if (IsKeyPressed(KEY_E)) { emgOn = !emgOn; Toast(emgOn ? "Emergency response ON" : "Emergency response OFF"); }
    if (IsKeyPressed(KEY_T)) ToggleAll();
    if (IsKeyPressed(KEY_L)) { if (hn >= 0) ToggleNode(hn); else Toast("Hover a junction, then press L"); }
    if (IsKeyPressed(KEY_V)) view3d = !view3d;
    if (IsKeyPressed(KEY_Q)) { quality = !quality; Toast(quality ? "3D quality: high" : "3D quality: low"); }
    if (IsKeyPressed(KEY_TAB)) { view3d = 1; camPreset = (camPreset + 1) % 4; if (camPreset == 3) PickFollow(); else followCar = followAmb = -1; if (camPreset == 1) userDist = 85; if (camPreset == 2) userDist = 58; }
    if (IsKeyPressed(KEY_F)) { view3d = 1; if (camPreset == 3) { camPreset = 0; followCar = followAmb = -1; } else { camPreset = 3; PickFollow(); } }
    if (IsKeyPressed(KEY_ZERO)) { camT = (Vector3){0, 0, 0}; camYaw = .35f; camPitch = .75f; userDist = 75; camPreset = 0; followCar = followAmb = -1; }
    if (!view3d && hn >= 0 && N[hn].sig && wh != 0) N[hn].cycle = Clamp(N[hn].cycle + wh * 2, 10, 60);
    if (IsMouseButtonPressed(MOUSE_LEFT_BUTTON)) {
      pressPos = mp; pressMap = Hover(R_MAP) && !Hover(tgl);
      for (int i = 0; i < 5; i++) if (Hover((Rectangle){660 + i * 82, 22, 76, 40})) { if (i == 0) DoCrash(); else if (i == 1) DoStadium(); else if (i == 2) DoRain(); else if (i == 3) DoWorks(); else DoMarket(); }
      for (int i = 0; i < 3; i++) if (Hover((Rectangle){1080 + i * 56, 26, 56, 32})) speedIdx = i;
      if (Hover(tgl)) view3d = mp.x > tgl.x + 48;
      if (Hover((Rectangle){28 + 3 * 248, 88, 232, 100})) ToggleAll();
    }
    if (IsMouseButtonReleased(MOUSE_LEFT_BUTTON) && pressMap && Vector2Distance(mp, pressPos) < 5 && hov) { /* a click, not a drag */
      int ctrl = IsKeyDown(KEY_LEFT_CONTROL) || IsKeyDown(KEY_RIGHT_CONTROL), shift = IsKeyDown(KEY_LEFT_SHIFT) || IsKeyDown(KEY_RIGHT_SHIFT);
      if (hb >= 0) selB = hb;
      else if (hn >= 0) { /* junctions are controlled with L */ }
      else if (he >= 0) {
        if (ctrl) StartWorks(he);
        else if (shift) StartCrash(E[he ^ 1].cnt > E[he].cnt ? he ^ 1 : he);
        else {
          char a[8], b[8], t[72]; E[he].closed = !E[he].closed; E[he ^ 1].closed = E[he].closed; routeCause = 2; Route();
          NName(E[he].a, a); NName(E[he].b, b); snprintf(t, 72, "Road %s - %s %s", a, b, E[he].closed ? "closed" : "reopened"); AddFeed(t, E[he].closed ? C_AMBER : C_GREEN);
        }
      } else selB = -1;
    }
    if (view3d) { /* 3D camera: drag orbit, shift+drag / right / middle drag / arrows pan */
      Vector2 md = GetMouseDelta(); float sy = sinf(camYaw), cw = cosf(camYaw), kp = camDist * .0012f, ps = camDist * .9f * dt;
      int shift = IsKeyDown(KEY_LEFT_SHIFT) || IsKeyDown(KEY_RIGHT_SHIFT), anyBtn = IsMouseButtonDown(MOUSE_LEFT_BUTTON) || IsMouseButtonDown(MOUSE_RIGHT_BUTTON) || IsMouseButtonDown(MOUSE_MIDDLE_BUTTON);
      if (IsMouseButtonPressed(MOUSE_LEFT_BUTTON) || IsMouseButtonPressed(MOUSE_RIGHT_BUTTON) || IsMouseButtonPressed(MOUSE_MIDDLE_BUTTON)) drag3d = Hover(R_MAP) && !Hover(tgl);
      if (!anyBtn) drag3d = 0;
      if (drag3d && IsMouseButtonDown(MOUSE_LEFT_BUTTON) && !shift && Vector2Length(md) > 0) { camYaw -= md.x * .006f; camPitch = Clamp(camPitch + md.y * .006f, .12f, 1.45f); camPreset = 0; followCar = followAmb = -1; }
      if (drag3d && (IsMouseButtonDown(MOUSE_RIGHT_BUTTON) || IsMouseButtonDown(MOUSE_MIDDLE_BUTTON) || (shift && IsMouseButtonDown(MOUSE_LEFT_BUTTON)))) {
        camT.x += (-cw * md.x - sy * md.y) * kp; camT.z += (sy * md.x - cw * md.y) * kp; camPreset = 0; followCar = followAmb = -1;
      }
      if (IsKeyDown(KEY_UP) || IsKeyDown(KEY_DOWN) || IsKeyDown(KEY_LEFT) || IsKeyDown(KEY_RIGHT)) {
        float fx = ((IsKeyDown(KEY_UP) ? 1 : 0) - (IsKeyDown(KEY_DOWN) ? 1 : 0)) * ps, rx = ((IsKeyDown(KEY_RIGHT) ? 1 : 0) - (IsKeyDown(KEY_LEFT) ? 1 : 0)) * ps;
        camT.x += -sy * fx + cw * rx; camT.z += -cw * fx - sy * rx; camPreset = 0; followCar = followAmb = -1;
      }
      if (Hover(R_MAP) && wh != 0) { if (camPreset == 3) followDist = Clamp(followDist * (1 - wh * .1f), 6, 60); else userDist = Clamp(userDist * (1 - wh * .1f), 12, 140); }
      UpdateCam3D(dt);
    }
    if (!paused) for (int k = 0; k < MULT[speedIdx]; k++) SimStep(dt);
    for (int i = 0; i < 5; i++) kpiD[i] = Appr(kpiD[i], kpiT[i], 6, dt);
    if (view3d) Render3D();

    BeginDrawing();
    ClearBackground(C_BG);
    Glow(120, 60, 520, C_VIOLET, .16f);
    Glow(SW - 100, SH - 40, 560, C_CYAN, .10f);
    DrawHeader();
    for (int i = 0; i < 5; i++) DrawKpi(i);
    if (view3d) DrawMap3D(); else DrawMap2D(hn, hb);
    DrawViewToggle(); DrawInfo(); if (hov) MapTips(hn, he, hb);
    DrawEvents(); DrawPurpose(); DrawEmerg();
    Txt("1 2 4 speed   C crash   S stadium   R rain   W works   M market   X clear   E ambulances   T all signals   L signals here   O fog   V 2D/3D   Tab camera   F chase   P pause", SW / 2, 780, 11, C_MUTED, 0, AC);
    DrawOverlay();
    if (introT < .6f) DrawRectangle(0, 0, SW, SH, Fade(C_BG, 1 - introT / .6f));
    EndDrawing();
    if (shotFrames && ++frame >= shotFrames) { TakeScreenshot(shotFile); break; }
  }
  UnloadRenderTexture(rt3); UnloadShader(sh3);
  CloseWindow();
  return 0;
}