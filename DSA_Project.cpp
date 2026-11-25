//  DungeonBound  -  a roguelike in ONE file (C++17 + SFML 3)
//  No files, no database: everything lives in memory.

//  Goal : survive, fight monsters, loot chests and reach the stairs on every floor.
//  Keys : WASD / Arrows = move (walk into a monster to attack)
//         E = drink potion   Space = wait a turn   Tab = show route to stairs
//         Enter = start game   R = restart (after death)   Esc = quit

//  DSA CONCEPTS USED (search for the tag, e.g. "[DSU]"):
//   [ARRAY]     2D arrays for the map, items, fog of war, distance map
//   [DSU]       Union-Find (Kruskal) builds a maze where every cell is reachable
//   [RECURSION] DSU find(), BST insert / traversal
//   [GRAPH/BFS] The map is a graph. BFS (queue) = enemy chasing, vision,
//               stairs placement and the route-to-stairs hint
//   [QUEUE]     BFS queue + message log (oldest message removed first)
//   [STACK]     Potion bag (last potion picked up is the first one used)
//   [LINKEDLIST] Gear list (every sword / armor you find is a new node)
//   [HASHMAP]   unordered_map: monster stats by name, monster lookup by tile
//   [HEAP]      priority_queue turn scheduler (fast monsters act more often)
//   [SORT]      std::sort the nearby monsters by distance
//   [BINSEARCH] binary search finds your level from your XP
//   [DP]        XP table built from earlier entries (dynamic programming)
//   [BST]       Leaderboard: binary search tree of scores

//  Build (MSYS2 UCRT64):
//   g++ DungeonBound.cpp -o DungeonBound.exe -std=c++17 -lsfml-graphics -lsfml-window -lsfml-system

#include <SFML/Graphics.hpp>
#include <algorithm>
#include <cmath>
#include <iostream>
#include <numeric>
#include <optional>
#include <queue>
#include <random>
#include <stack>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;

// constants
const int MW = 31, MH = 21;                 // map size in tiles (odd numbers for the maze)
const int TILE = 28;                        // tile size in pixels
const int SIDE = 200;                       // width of the right sidebar
const int HUD = 130;                        // height of the bottom panel
const int MAP_W = MW * TILE, MAP_H = MH * TILE;
const int WIN_W = MAP_W + SIDE, WIN_H = MAP_H + HUD;
const int VIEW = 6;                         // how many steps you can see
const int DX[4] = {0, 0, -1, 1};
const int DY[4] = {-1, 1, 0, 0};

typedef sf::Color Col;
const Col WHITE(235, 235, 245), GREY(150, 150, 170), GOLD(255, 210, 60), RED(240, 80, 90);
const Col GREEN(110, 230, 140), CYAN(120, 220, 255), PURPLE(180, 130, 255), ORANGE(255, 160, 60);

// Random number helpers: rnd(a,b) = random int in [a,b], rndf() = random float in [-1,1].
mt19937 rng(random_device{}());
int rnd(int a, int b) { return uniform_int_distribution<int>(a, b)(rng); }
float rndf() { return rnd(-100, 100) / 100.f; }          // random float in [-1, 1]

// The one font used for all text (loaded in main).
sf::Font font;

// [DSU]
// DSU (Union-Find): tracks which maze cells are already connected.
//   find(x)     -> the 'leader' of the group x belongs to
//   unite(a,b)  -> joins two groups, returns false if they were already joined
struct DSU {
    vector<int> parent;
    DSU(int n) : parent(n) { iota(parent.begin(), parent.end(), 0); }
    // Returns the leader of x's group. Path compression flattens the tree for speed.
    int find(int x) {                                   // [RECURSION]
        if (parent[x] == x) return x;
        return parent[x] = find(parent[x]);
    }
    // Merges the groups of a and b. Returns true only if they were separate before.
    bool unite(int a, int b) {                          // false if already connected
        a = find(a); b = find(b);
        if (a == b) return false;
        parent[a] = b;
        return true;
    }
};

// [LINKEDLIST]
// One node of the gear linked list (each item you find is a node pointing to the next).
struct GearNode {
    string name;
    int bonus;
    bool armor;          // false = weapon (attack), true = armor (defense)
    GearNode* next;
};

// [BST]
// One node of the leaderboard Binary Search Tree: smaller scores go left, bigger go right.
struct ScoreNode {
    int score, floor;
    ScoreNode *left = nullptr, *right = nullptr;
};
// Inserts a score into the BST recursively and returns the (possibly new) subtree root.
ScoreNode* insertScore(ScoreNode* n, int score, int floor) {   // [RECURSION]
    if (!n) { n = new ScoreNode; n->score = score; n->floor = floor; return n; }
    if (score < n->score) n->left = insertScore(n->left, score, floor);
    else n->right = insertScore(n->right, score, floor);
    return n;
}
// Collects up to 'limit' best scores into 'out'. Visiting right -> node -> left gives high-to-low order.
// reverse in-order walk = scores from highest to lowest
void topScores(ScoreNode* n, vector<pair<int, int>>& out, size_t limit) {
    if (!n || out.size() >= limit) return;
    topScores(n->right, out, limit);
    if (out.size() < limit) out.push_back({n->score, n->floor});
    topScores(n->left, out, limit);
}
// Deletes every node of the BST (post-order) so no memory leaks at exit.
void freeTree(ScoreNode* n) {
    if (!n) return;
    freeTree(n->left); freeTree(n->right); delete n;
}
ScoreNode* leaderboard = nullptr;     // lives as long as the program runs

// [HASHMAP]
// Base stats of a monster type, stored in the hash map below.
struct Stats { int hp, atk, speed, xp; Col color; };
unordered_map<string, Stats> bestiary = {
    {"Bat",    {6,  2, 7,  5,  Col(180, 120, 255)}},   // fast, weak
    {"Goblin", {10, 3, 10, 8,  Col(90, 200, 90)}},     // average
    {"Slime",  {14, 2, 15, 6,  Col(70, 200, 220)}},    // slow, tanky
    {"Ogre",   {24, 5, 18, 16, Col(210, 120, 70)}},    // very slow, hits hard (floor 3+)
};
// Names used to pick a random monster type (index into the bestiary).
const vector<string> monsterNames = {"Bat", "Goblin", "Slime", "Ogre"};

// One monster on the current floor.
struct Enemy {
    string name;
    int x, y, hp, maxHp, atk, speed, xp;
    bool alive;
    Col color;
    float fx = 0, fy = 0, flash = 0;     // smooth drawing position + hit flash
};

// small effect types
// Small helper structs for visual effects and the message log:
//   Msg      = one line of the event log with its colour
//   Floater  = floating text (damage numbers) that rises and fades
//   Particle = tiny coloured square used for bursts and embers
struct Msg      { string text; Col color; };
struct Floater  { float x, y; string text; Col color; float life; };
struct Particle { float x, y, vx, vy, life, maxLife, size, grav; Col color; };


// Game holds ALL the game state (map, hero, monsters, data structures) and the rules (methods).
struct Game {
    enum class State { Menu, Play, Dead };
    State state = State::Menu;

    int grid[MH][MW];        // [ARRAY] 1 = wall, 0 = floor
    char item[MH][MW];       // '.' nothing  p potion  g gold  s sword  c chest  t hidden trap  T seen trap
    bool seen[MH][MW];       // fog of war memory
    int dist[MH][MW];        // BFS distance from the player (-1 = unreachable)

    int px, py, hp, maxHp, xp, gold, kills, floorNo, lvl, clockTime;
    int stairsX, stairsY;

    vector<Enemy> enemies;
    unordered_map<int, int> enemyAt;                                  // [HASHMAP] tile -> enemy index
    priority_queue<pair<int, int>, vector<pair<int, int>>,
                   greater<pair<int, int>>> turnQ;                    // [HEAP] (time, enemy index)
    stack<int> potions;                                               // [STACK] heal amounts
    queue<Msg> log;                                                   // [QUEUE] message log
    GearNode* gear = nullptr;                                         // [LINKEDLIST]
    vector<int> xpNeed;                                               // [DP] xp needed per level

    // visual state
    vector<Floater> floaters;
    vector<Particle> parts;
    float time = 0, shake = 0, flash = 0, banner = 0, drawX = 0, drawY = 0;
    bool showPath = false;

    // Constructor: builds the XP table (DP), prepares a first game, then shows the menu.
    Game() {
        // [DP] each level needs more than the one before, built from earlier entries
        xpNeed = {0, 10};
        for (int i = 2; i < 30; i++) xpNeed.push_back(xpNeed[i - 1] + xpNeed[i - 2] / 2 + 10);
        newGame();
        state = State::Menu;
    }
    // Destructor: frees the gear linked list.
    ~Game() { clearGear(); }

    // Deletes every node of the gear linked list.
    void clearGear() {
        while (gear) { GearNode* t = gear; gear = gear->next; delete t; }
    }

    // Adds a message to the log queue; the oldest one is removed when more than 5 exist.
    void say(const string& s, Col c = WHITE) {
        log.push({s, c});
        while (log.size() > 5) log.pop();     // drop the oldest message
    }

    // Resets the hero and all data structures, then builds floor 1 and starts playing.
    void newGame() {
        clearGear();
        while (!potions.empty()) potions.pop();
        while (!log.empty()) log.pop();
        floaters.clear(); parts.clear();
        hp = maxHp = 30; xp = 0; gold = 0; kills = 0; floorNo = 1; lvl = 1;
        state = State::Play;
        buildFloor();
        say("You enter the dungeon. Find the stairs!", CYAN);
    }

    // [BINSEARCH] level = how many thresholds are <= xp
    // Binary search over the XP table: returns the hero level for the current XP.
    int levelFromXp() const {
        return int(upper_bound(xpNeed.begin(), xpNeed.end(), xp) - xpNeed.begin());
    }

    // walk the linked list and add up the bonuses
    // Walks the gear linked list and sums the bonus (armor=false -> attack, armor=true -> defense).
    int gearBonus(bool armor) const {
        int sum = 0;
        for (GearNode* g = gear; g; g = g->next)
            if (g->armor == armor) sum += g->bonus;
        return sum;
    }

    // Final score formula: gold + 50 per floor + 10 per kill.
    int score() const { return gold + floorNo * 50 + kills * 10; }

    // visual effects
    // Spawns floating text (like '-5') above the tile (tx, ty).
    void addFloater(float tx, float ty, const string& text, Col c) {
        floaters.push_back({tx * TILE + TILE / 2.f, ty * TILE, text, c, 1.1f});
    }

    // Spawns n particles flying outward from tile (tx, ty) - used for hits, kills, loot.
    void burst(float tx, float ty, Col c, int n, float speed = 90) {
        for (int i = 0; i < n; i++) {
            float a = rnd(0, 628) / 100.f, s = rnd(30, 100) / 100.f * speed;
            float life = 0.5f + rnd(0, 50) / 100.f;
            parts.push_back({tx * TILE + TILE / 2.f, ty * TILE + TILE / 2.f, cos(a) * s, sin(a) * s - 30,
                             life, life, float(rnd(2, 4)), 220, c});
        }
    }

    // Called every frame: advances animations (shake, flash, sliding movement, floaters, particles).
    // dt = seconds since last frame, so animation speed is the same on every computer.
    void update(float dt) {
        time += dt;
        shake = max(0.f, shake - dt * 30);
        flash = max(0.f, flash - dt * 2.2f);
        banner = max(0.f, banner - dt);

        float k = min(1.f, dt * 16);                       // smooth sliding of characters
        drawX += (px - drawX) * k;
        drawY += (py - drawY) * k;
        for (auto& e : enemies) {
            e.fx += (e.x - e.fx) * k;
            e.fy += (e.y - e.fy) * k;
            e.flash = max(0.f, e.flash - dt * 5);
        }
        for (auto& f : floaters) { f.y -= 32 * dt; f.life -= dt; }
        floaters.erase(remove_if(floaters.begin(), floaters.end(),
                       [](const Floater& f) { return f.life <= 0; }), floaters.end());

        if (state == State::Menu && rnd(1, 100) <= 40)     // embers rising on the menu
            parts.push_back({float(rnd(0, WIN_W)), float(WIN_H + 5), rndf() * 15, -rnd(30, 90) * 1.f,
                             4.f, 4.f, float(rnd(2, 4)), 0, rnd(0, 1) ? ORANGE : GOLD});
        for (auto& p : parts) { p.x += p.vx * dt; p.y += p.vy * dt; p.vy += p.grav * dt; p.life -= dt; }
        parts.erase(remove_if(parts.begin(), parts.end(),
                    [](const Particle& p) { return p.life <= 0; }), parts.end());
    }

    // build a floor
    // Step 1 of floor creation: clears the map and carves a maze using Kruskal + DSU,
    // then opens a few extra doors (loops) and some 3x3 rooms.
    void carveMaze() {
        for (int y = 0; y < MH; y++)
            for (int x = 0; x < MW; x++) { grid[y][x] = 1; item[y][x] = '.'; seen[y][x] = false; }

        // [DSU] Kruskal maze: cells sit on odd coordinates, walls sit between them
        int CW = (MW - 1) / 2, CH = (MH - 1) / 2;
        struct Wall { int x, y, a, b; };
        vector<Wall> walls;
        for (int cy = 0; cy < CH; cy++)
            for (int cx = 0; cx < CW; cx++) {
                int id = cy * CW + cx;
                grid[2 * cy + 1][2 * cx + 1] = 0;
                if (cx + 1 < CW) walls.push_back({2 * cx + 2, 2 * cy + 1, id, id + 1});
                if (cy + 1 < CH) walls.push_back({2 * cx + 1, 2 * cy + 2, id, id + CW});
            }
        shuffle(walls.begin(), walls.end(), rng);
        DSU dsu(CW * CH);
        for (auto& w : walls) {
            if (dsu.unite(w.a, w.b)) grid[w.y][w.x] = 0;          // joins two separate areas
            else if (rnd(1, 100) <= 10) grid[w.y][w.x] = 0;       // extra door = loops
        }
        // a few open rooms
        for (int i = 0; i < 5; i++) {
            int rx = rnd(1, MW - 5), ry = rnd(1, MH - 5);
            for (int y = ry; y < ry + 3; y++)
                for (int x = rx; x < rx + 3; x++) grid[y][x] = 0;
        }
    }

    // [GRAPH/BFS] distance from the player to every tile, using a queue
    // Breadth-First Search from the hero: fills dist[][] with the number of steps to every tile.
    // Used for monster chasing, vision range, stairs placement and the route hint.
    void bfs() {
        for (int y = 0; y < MH; y++) for (int x = 0; x < MW; x++) dist[y][x] = -1;
        queue<pair<int, int>> q;
        dist[py][px] = 0;
        q.push({px, py});
        while (!q.empty()) {
            auto [x, y] = q.front(); q.pop();
            for (int d = 0; d < 4; d++) {
                int nx = x + DX[d], ny = y + DY[d];
                if (grid[ny][nx] == 0 && dist[ny][nx] == -1) {
                    dist[ny][nx] = dist[y][x] + 1;
                    q.push({nx, ny});
                }
            }
        }
    }

    // A tile is visible if it is a floor within VIEW steps of the hero.
    bool visible(int x, int y) const { return grid[y][x] == 0 && dist[y][x] >= 0 && dist[y][x] <= VIEW; }

    // Marks currently visible tiles (and walls touching them) as 'seen' so the map remembers them.
    void updateFog() {
        for (int y = 0; y < MH; y++)
            for (int x = 0; x < MW; x++)
                if (visible(x, y)) seen[y][x] = true;
        // walls next to a seen floor tile are also remembered
        for (int y = 1; y < MH - 1; y++)
            for (int x = 1; x < MW - 1; x++)
                if (grid[y][x] == 1)
                    for (int dy = -1; dy <= 1; dy++)
                        for (int dx = -1; dx <= 1; dx++)
                            if (grid[y + dy][x + dx] == 0 && seen[y + dy][x + dx]) seen[y][x] = true;
    }

    // Creates a whole new floor: maze, hero start, stairs (farthest tile via BFS),
    // monsters (with stats from the hash map), potions, gold, chests, traps and swords.
    void buildFloor() {
        carveMaze();
        px = 1; py = 1;
        drawX = float(px); drawY = float(py);
        bfs();

        // the stairs go to the floor tile that is farthest away (BFS result)
        int best = -1;
        for (int y = 0; y < MH; y++)
            for (int x = 0; x < MW; x++)
                if (dist[y][x] > best) { best = dist[y][x]; stairsX = x; stairsY = y; }

        vector<pair<int, int>> spots;
        for (int y = 0; y < MH; y++)
            for (int x = 0; x < MW; x++)
                if (dist[y][x] >= 6 && !(x == stairsX && y == stairsY)) spots.push_back({x, y});
        shuffle(spots.begin(), spots.end(), rng);

        enemies.clear(); enemyAt.clear();
        turnQ = {};                                  // empty the heap
        clockTime = 0;

        int count = min(3 + floorNo, 12);
        int pool = floorNo >= 3 ? 4 : 3;             // ogres appear from floor 3
        for (int i = 0; i < count && !spots.empty(); i++) {
            string name = monsterNames[rnd(0, pool - 1)];
            Stats s = bestiary[name];                // [HASHMAP] lookup by name
            int up = floorNo - 1;
            Enemy e{name, spots.back().first, spots.back().second,
                    s.hp + up * 2, s.hp + up * 2, s.atk + up / 2, s.speed, s.xp, true, s.color};
            e.fx = float(e.x); e.fy = float(e.y);
            spots.pop_back();
            enemyAt[e.y * MW + e.x] = (int)enemies.size();
            turnQ.push({e.speed, (int)enemies.size()});   // [HEAP] first action time
            enemies.push_back(e);
        }
        auto drop = [&](char c, int n) {
            for (int i = 0; i < n && !spots.empty(); i++) {
                item[spots.back().second][spots.back().first] = c;
                spots.pop_back();
            }
        };
        drop('p', 2);
        drop('g', 5);
        drop('c', rnd(1, 2));
        drop('t', 2 + floorNo / 2);
        if (rnd(1, 100) <= 60) drop('s', 1);
        updateFog();
        banner = 2.2f;
    }

    // gameplay
    // Adds XP and handles level-ups (more max HP, partial heal, effects).
    void gainXp(int n) {
        xp += n;
        int newLvl = levelFromXp();
        while (lvl < newLvl) {
            lvl++; maxHp += 5; hp = min(maxHp, hp + 8);
            say("LEVEL UP! You are level " + to_string(lvl), CYAN);
            addFloater(float(px), float(py) - 0.6f, "LEVEL UP!", CYAN);
            burst(float(px), float(py), GOLD, 22, 130);
        }
    }

    // Applies damage to the hero with screen shake, red flash, number popup; calls die() at 0 HP.
    void hurtPlayer(int dmg) {
        hp -= dmg;
        flash = 0.55f;
        shake = max(shake, 7.f);
        addFloater(float(px), float(py), "-" + to_string(dmg), RED);
        burst(float(px), float(py), RED, 8);
        if (hp <= 0) die();
    }

    // Hero hits the monster at index idx. Damage = 2 + level + weapon bonus + luck.
    // If it dies: gives XP + gold, maybe drops a potion, removes it from the hash map.
    void playerAttack(int idx) {
        Enemy& e = enemies[idx];
        int dmg = 2 + lvl + gearBonus(false) + rnd(0, 2);
        e.hp -= dmg;
        e.flash = 1;
        shake = max(shake, 3.f);
        addFloater(float(e.x), float(e.y), to_string(dmg), WHITE);
        if (e.hp > 0) { say("You hit the " + e.name + " for " + to_string(dmg), GREY); burst(float(e.x), float(e.y), e.color, 5); return; }
        e.alive = false;
        enemyAt.erase(e.y * MW + e.x);
        kills++;
        gold += rnd(1, 5);
        say("You slay the " + e.name + "! +" + to_string(e.xp) + " xp", GOLD);
        burst(float(e.x), float(e.y), e.color, 18, 120);
        if (item[e.y][e.x] == '.' && rnd(1, 100) <= 25) item[e.y][e.x] = 'p';   // drop
        gainXp(e.xp);
    }

    // Adds a Sword or Armor node at the head of the gear linked list.
    void giveGear(bool armor) {
        int b = rnd(1, 2);
        string name = string(armor ? "Armor +" : "Sword +") + to_string(b);
        gear = new GearNode{name, b, armor, gear};                  // add node at the head
        say("You find " + name + "!", CYAN);
        addFloater(float(px), float(py), name, CYAN);
    }

    // Pushes a new potion (random heal amount) onto the potion stack.
    void givePotion() {
        potions.push(rnd(10, 18));                                  // push on the stack
        say("You pick up a potion.", GREEN);
    }

    // Handles whatever lies on the hero's tile: potion, gold, sword, chest or spike trap.
    void pickUp() {
        char c = item[py][px];
        if (c == 'p') givePotion();
        if (c == 'g') {
            int g = rnd(5, 15) * floorNo;
            gold += g;
            say("You find " + to_string(g) + " gold.", GOLD);
            addFloater(float(px), float(py), "+" + to_string(g) + "g", GOLD);
        }
        if (c == 's') giveGear(false);
        if (c == 'c') {                                             // chest: random loot
            int r = rnd(1, 100);
            say("You open a chest!", GOLD);
            burst(float(px), float(py), GOLD, 14);
            if (r <= 30) giveGear(rnd(0, 1) == 1);
            else if (r <= 60) { givePotion(); givePotion(); }
            else { int g = rnd(20, 40) * floorNo; gold += g; say("It holds " + to_string(g) + " gold!", GOLD); }
        }
        if (c == 't' || c == 'T') {                                 // spike trap
            int dmg = 3 + floorNo;
            say("Spikes! You take " + to_string(dmg) + " damage.", RED);
            item[py][px] = 'T';
            hurtPlayer(dmg);
            return;
        }
        item[py][px] = '.';
    }

    // One monster's action: attack if next to the hero, otherwise step along the BFS distances toward the hero.
    void enemyAct(int i) {
        Enemy& e = enemies[i];
        int d = dist[e.y][e.x];
        if (d == 1) {                                         // next to the player: attack
            int dmg = max(1, e.atk + rnd(0, 1) - gearBonus(true));
            say(e.name + " hits you for " + to_string(dmg), RED);
            hurtPlayer(dmg);
        } else if (d > 1 && d <= 12) {                        // chase: step to a tile closer by BFS
            for (int k = 0; k < 4; k++) {
                int nx = e.x + DX[k], ny = e.y + DY[k];
                if (grid[ny][nx] == 0 && dist[ny][nx] == d - 1 && !enemyAt.count(ny * MW + nx)) {
                    enemyAt.erase(e.y * MW + e.x);
                    e.x = nx; e.y = ny;
                    enemyAt[ny * MW + nx] = i;
                    break;
                }
            }
        }
    }

    // Ends the hero's turn: recompute BFS/fog, advance time, then let every monster whose
    // turn is due act (the priority queue always gives the earliest turn first).
    // [HEAP] player acts, time moves forward, every monster whose turn has come acts
    void endTurn() {
        bfs();
        updateFog();
        clockTime += 10;
        while (!turnQ.empty() && turnQ.top().first <= clockTime && state == State::Play) {
            auto [t, i] = turnQ.top(); turnQ.pop();
            if (!enemies[i].alive) continue;
            enemyAct(i);
            turnQ.push({t + enemies[i].speed, i});
        }
    }

    // Hero died: switch to the Dead state and insert the score into the leaderboard BST.
    void die() {
        state = State::Dead;
        say("You died...", RED);
        leaderboard = insertScore(leaderboard, score(), floorNo);
    }

    // Hero moves/attacks in direction (dx,dy): attack a monster there, or walk onto a free tile,
    // pick up items, check the stairs. Bumping a wall costs no turn.
    void playerMove(int dx, int dy) {
        if (state != State::Play) return;
        int nx = px + dx, ny = py + dy;
        auto it = enemyAt.find(ny * MW + nx);
        if (it != enemyAt.end()) playerAttack(it->second);
        else if (grid[ny][nx] == 0) {
            px = nx; py = ny;
            pickUp();
            if (state != State::Play) return;                 // died on a trap
            if (px == stairsX && py == stairsY) {             // next floor
                floorNo++;
                hp = min(maxHp, hp + 6);
                buildFloor();
                say("You descend to floor " + to_string(floorNo), CYAN);
                return;
            }
        } else return;                                        // bumped a wall: no turn used
        endTurn();
    }

    // Drinks the top potion of the stack (last picked up) and heals; takes one turn.
    void usePotion() {
        if (state != State::Play) return;
        if (potions.empty()) { say("You have no potions.", GREY); return; }
        int heal = potions.top(); potions.pop();              // last in, first out
        hp = min(maxHp, hp + heal);
        say("You drink a potion (+" + to_string(heal) + " hp)", GREEN);
        addFloater(float(px), float(py), "+" + to_string(heal), GREEN);
        burst(float(px), float(py), GREEN, 10, 60);
        endTurn();
    }
    // Skip a turn (monsters still move).
    void wait() { if (state == State::Play) endTurn(); }
};

//  Drawing helpers
// ============================================================================
// Returns the colour c made darker; f = 1 keeps it, f = 0.5 halves the brightness.
Col shade(Col c, float f) {                       // darken a colour (f = 0..1)
    return Col((uint8_t)(c.r * f), (uint8_t)(c.g * f), (uint8_t)(c.b * f), c.a);
}
// Returns the colour c with transparency a (0 = invisible, 1 = solid).
Col withAlpha(Col c, float a) { return Col(c.r, c.g, c.b, (uint8_t)(max(0.f, min(1.f, a)) * 255)); }

// Draws a text string at (x,y). shadow=true adds a dark outline for readability.
void drawText(sf::RenderWindow& w, const string& s, float x, float y, unsigned size, Col c, bool shadow = false) {
    sf::Text t(font, s, size);
    if (shadow) {
        t.setFillColor(Col(0, 0, 0, (uint8_t)(c.a * 0.7f)));
        t.setPosition({x + 1, y + 1});
        w.draw(t);
    }
    t.setFillColor(c);
    t.setPosition({x, y});
    w.draw(t);
}

// Draws text horizontally centered around x = cx.
void drawTextC(sf::RenderWindow& w, const string& s, float cx, float y, unsigned size, Col c) {   // centered
    sf::Text t(font, s, size);
    sf::FloatRect b = t.getLocalBounds();
    drawText(w, s, cx - (b.position.x + b.size.x / 2), y, size, c, true);
}

// Draws a filled rectangle.
void drawRect(sf::RenderWindow& w, float x, float y, float rw, float rh, Col c) {
    sf::RectangleShape r({rw, rh});
    r.setPosition({x, y});
    r.setFillColor(c);
    w.draw(r);
}

// Draws a filled circle (or a triangle/polygon when pts is small); sx/sy stretch it.
void drawCircle(sf::RenderWindow& w, float x, float y, float r, Col c, float sx = 1, float sy = 1, size_t pts = 24) {
    sf::CircleShape s(r, pts);
    s.setFillColor(c);
    s.setPosition({x, y});
    s.setScale({sx, sy});
    w.draw(s);
}

// Draws a progress bar (HP, XP...) filled to 'frac' (0..1) with an optional centered label.
void drawBar(sf::RenderWindow& w, float x, float y, float bw, float bh, float frac, Col c, const string& label = "") {
    sf::RectangleShape back({bw, bh});
    back.setPosition({x, y});
    back.setFillColor(Col(35, 32, 48));
    back.setOutlineThickness(1);
    back.setOutlineColor(Col(110, 100, 140));
    w.draw(back);
    float f = max(0.f, min(1.f, frac));
    drawRect(w, x, y, bw * f, bh, c);
    drawRect(w, x, y, bw * f, bh / 3, Col(255, 255, 255, 50));       // shine
    if (!label.empty()) drawTextC(w, label, x + bw / 2, y - 1, (unsigned)max(10.f, bh - 3), WHITE);
}

// Draws a framed HUD box with a title strip.
void drawPanel(sf::RenderWindow& w, float x, float y, float pw, float ph, const string& title) {
    sf::RectangleShape r({pw, ph});
    r.setPosition({x, y});
    r.setFillColor(Col(20, 18, 30));
    r.setOutlineThickness(-2);
    r.setOutlineColor(Col(85, 75, 125));
    w.draw(r);
    drawRect(w, x + 2, y + 2, pw - 4, 20, Col(45, 38, 72));
    drawText(w, title, x + 8, y + 3, 14, Col(200, 190, 240));
}

// how bright a tile is, based on how far it is from the torch
// Brightness of a tile from its BFS distance: closer to the hero = brighter.
float light(int d) { return d < 0 ? 0.32f : max(0.42f, 1.0f - d * 0.1f); }

// Brightness for a tile on the map (floors by distance, walls by their nearest lit floor, remembered = dim).
float tileLight(Game& g, int x, int y) {
    if (g.grid[y][x] == 0) return g.visible(x, y) ? light(g.dist[y][x]) : 0.32f;
    int best = 99;                                    // walls take the light of nearby visible floor
    for (int dy = -1; dy <= 1; dy++)
        for (int dx = -1; dx <= 1; dx++)
            if (g.visible(x + dx, y + dy)) best = min(best, g.dist[y + dy][x + dx]);
    return best == 99 ? 0.32f : light(best);
}

// Draws one wall tile with a lit top edge, shaded bottom and brick lines.
void drawWallTile(sf::RenderWindow& w, float px, float py, float f, int x, int y) {
    drawRect(w, px, py, TILE, TILE, shade(Col(92, 82, 120), f));
    drawRect(w, px, py, TILE, 4, shade(Col(140, 128, 172), f));               // lit top edge
    drawRect(w, px, py + TILE - 5, TILE, 5, shade(Col(52, 46, 74), f));       // shaded bottom
    drawRect(w, px, py + TILE / 2, TILE, 1, shade(Col(58, 50, 82), f));       // brick lines
    drawRect(w, px + ((y % 2) ? 8.f : 19.f), py + 4, 1, TILE / 2 - 4, shade(Col(58, 50, 82), f));
    drawRect(w, px + ((x % 2) ? 20.f : 9.f), py + TILE / 2, 1, TILE / 2 - 5, shade(Col(58, 50, 82), f));
}

// Draws one floor tile with small variations so it does not look flat.
void drawFloorTile(sf::RenderWindow& w, float px, float py, float f, int x, int y) {
    int v = (x * 37 + y * 91) % 7;                    // small variation so the floor is not flat
    drawRect(w, px, py, TILE, TILE, shade(Col(28, 26, 38), f));
    drawRect(w, px + 1, py + 1, TILE - 2, TILE - 2, shade(Col(uint8_t(58 + v * 3), uint8_t(54 + v * 3), uint8_t(76 + v * 3)), f));
    if (v == 3) drawRect(w, px + 8, py + 10, 3, 3, shade(Col(100, 95, 120), f));
    if (v == 5) drawRect(w, px + 17, py + 18, 4, 2, shade(Col(42, 40, 56), f));
}

// Draws the animated, pulsing golden staircase.
void drawStairs(sf::RenderWindow& w, float px, float py, float t) {
    float pulse = 0.75f + 0.25f * sin(t * 3);
    drawCircle(w, px + 2, py + 2, 12, Col(255, 220, 90, (uint8_t)(40 * pulse)));
    for (int i = 0; i < 4; i++)                                               // little staircase
        drawRect(w, px + 5 + i * 3, py + 6 + i * 5, 18 - i * 3, 5, shade(GOLD, pulse - i * 0.12f));
}

// Draws a floor item by its code: p potion, g gold, s sword, c chest, T revealed trap.
void drawItem(sf::RenderWindow& w, char it, float px, float py, float t) {
    float bob = sin(t * 3 + px) * 1.5f;
    if (it == 'p') {                                                          // potion
        drawRect(w, px + 9, py + 11 + bob, 10, 11, Col(225, 55, 85));
        drawRect(w, px + 11, py + 7 + bob, 6, 5, Col(190, 220, 240));
        drawRect(w, px + 12, py + 5 + bob, 4, 3, Col(130, 90, 50));
        drawRect(w, px + 11, py + 13 + bob, 2, 6, Col(255, 150, 170));
    } else if (it == 'g') {                                                   // gold coin
        drawCircle(w, px + 7, py + 8 + bob, 7, Col(235, 180, 30));
        drawCircle(w, px + 10, py + 11 + bob, 4, Col(255, 230, 110));
    } else if (it == 's') {                                                   // sword
        drawRect(w, px + 13, py + 3 + bob, 3, 17, Col(190, 235, 255));
        drawRect(w, px + 9, py + 19 + bob, 11, 3, Col(200, 150, 50));
        drawRect(w, px + 13, py + 22 + bob, 3, 4, Col(120, 80, 40));
    } else if (it == 'c') {                                                   // chest
        drawRect(w, px + 5, py + 10, 18, 13, Col(140, 90, 45));
        drawRect(w, px + 5, py + 10, 18, 5, Col(105, 65, 30));
        drawRect(w, px + 12, py + 13, 4, 5, GOLD);
    } else if (it == 'T') {                                                   // revealed trap
        for (int i = 0; i < 3; i++) drawCircle(w, px + 3 + i * 8.f, py + 12, 5, Col(170, 170, 185), 1, 1.4f, 3);
    }
}

// Draws one small square eye (used by monsters).
void drawEye(sf::RenderWindow& w, float x, float y, Col c) {
    drawRect(w, x, y, 4, 4, c);
}

// Draws one monster with its own look and animation, plus a health bar when hurt.
void drawEnemy(sf::RenderWindow& w, Enemy& e, float t) {
    float x = e.fx * TILE, y = e.fy * TILE;
    Col c = e.flash > 0.3f ? Col(255, 255, 255) : e.color;
    float bob = sin(t * 5 + e.x * 1.7f) * 1.5f;
    drawCircle(w, x + 5, y + 21, 10, Col(0, 0, 0, 90), 1, 0.35f);               // shadow

    if (e.name == "Slime") {
        float sq = 1 + 0.08f * sin(t * 6 + e.y);
        drawCircle(w, x + 3, y + 9 + bob, 11, c, 1.1f * sq, 0.85f / sq);
        drawCircle(w, x + 8, y + 12 + bob, 3, Col(255, 255, 255, 120));
        drawEye(w, x + 9, y + 14 + bob, Col(20, 20, 40)); drawEye(w, x + 16, y + 14 + bob, Col(20, 20, 40));
    } else if (e.name == "Bat") {
        float flap = 3 * sin(t * 14 + e.x);
        drawRect(w, x + 0, y + 9 + bob - flap, 10, 5 + flap, shade(c, 0.75f));      // wings
        drawRect(w, x + 18, y + 9 + bob - flap, 10, 5 + flap, shade(c, 0.75f));
        drawCircle(w, x + 8, y + 8 + bob, 6, c);                                    // body
        drawCircle(w, x + 7, y + 4 + bob, 2, c, 1, 1.5f, 3);                        // ears
        drawCircle(w, x + 15, y + 4 + bob, 2, c, 1, 1.5f, 3);
        drawEye(w, x + 10, y + 11 + bob, Col(255, 80, 80)); drawEye(w, x + 15, y + 11 + bob, Col(255, 80, 80));
    } else if (e.name == "Goblin") {
        drawRect(w, x + 7, y + 12 + bob, 14, 12, shade(c, 0.8f));                   // body
        drawCircle(w, x + 8, y + 3 + bob, 6, c);                                    // head
        drawCircle(w, x + 3, y + 5 + bob, 3, c, 1, 1, 3);                           // ears
        drawCircle(w, x + 19, y + 5 + bob, 3, c, 1, 1, 3);
        drawEye(w, x + 10, y + 7 + bob, Col(255, 240, 80)); drawEye(w, x + 15, y + 7 + bob, Col(255, 240, 80));
        drawRect(w, x + 22, y + 12 + bob, 3, 10, Col(160, 160, 170));               // dagger
    } else {                                                                        // Ogre
        drawRect(w, x + 3, y + 10 + bob, 22, 15, shade(c, 0.8f));                   // body
        drawRect(w, x + 7, y + 2 + bob, 14, 11, c);                                 // head
        drawCircle(w, x + 4, y + 1 + bob, 3, Col(235, 225, 200), 1, 1.3f, 3);       // horns
        drawCircle(w, x + 20, y + 1 + bob, 3, Col(235, 225, 200), 1, 1.3f, 3);
        drawEye(w, x + 10, y + 6 + bob, Col(255, 60, 60)); drawEye(w, x + 16, y + 6 + bob, Col(255, 60, 60));
        drawRect(w, x + 10, y + 11 + bob, 2, 3, WHITE); drawRect(w, x + 16, y + 11 + bob, 2, 3, WHITE);   // tusks
    }
    if (e.hp < e.maxHp) drawBar(w, x + 3, y - 2, TILE - 6, 5, float(e.hp) / e.maxHp, RED);
}

// Draws the hero (armor, helmet, plume, sword) with a gentle bobbing animation.
void drawPlayer(sf::RenderWindow& w, Game& g) {
    float x = g.drawX * TILE, y = g.drawY * TILE, bob = sin(g.time * 4) * 1.1f;
    drawCircle(w, x + 4, y + 21, 10, Col(0, 0, 0, 100), 1, 0.35f);                  // shadow
    drawRect(w, x + 7, y + 12 + bob, 14, 12, Col(80, 140, 235));                    // armor
    drawRect(w, x + 7, y + 20 + bob, 14, 4, Col(55, 100, 190));                     // belt
    drawCircle(w, x + 8, y + 3 + bob, 6, Col(245, 205, 170));                       // face
    drawRect(w, x + 8, y + 3 + bob, 12, 4, Col(190, 195, 215));                     // helmet
    drawRect(w, x + 13, y + 0 + bob, 3, 4, RED);                                    // plume
    drawRect(w, x + 10, y + 8 + bob, 2, 2, Col(30, 30, 40));                        // eyes
    drawRect(w, x + 16, y + 8 + bob, 2, 2, Col(30, 30, 40));
    drawRect(w, x + 22, y + 9 + bob, 3, 13, Col(200, 235, 255));                    // sword
    drawRect(w, x + 20, y + 20 + bob, 7, 2, GOLD);
}

// Draws everything inside the map area: tiles, items, route hint, torch glow, monsters, hero, effects.
void drawWorld(sf::RenderWindow& w, Game& g) {
    // tiles
    for (int y = 0; y < MH; y++)
        for (int x = 0; x < MW; x++) {
            if (!g.seen[y][x]) continue;
            float px = float(x * TILE), py = float(y * TILE), f = tileLight(g, x, y);
            if (g.grid[y][x] == 1) { drawWallTile(w, px, py, f, x, y); continue; }
            drawFloorTile(w, px, py, f, x, y);
            if (x == g.stairsX && y == g.stairsY) drawStairs(w, px, py, g.time);
            char it = g.item[y][x];
            if (it == 'T' || (g.visible(x, y) && it != '.' && it != 't')) drawItem(w, it, px, py, g.time);
        }

    // route to the stairs: walk back along the BFS distances [GRAPH/BFS]
    if (g.showPath && g.dist[g.stairsY][g.stairsX] > 0) {
        int cx = g.stairsX, cy = g.stairsY;
        while (g.dist[cy][cx] > 1) {
            for (int d = 0; d < 4; d++) {
                int nx = cx + DX[d], ny = cy + DY[d];
                if (g.grid[ny][nx] == 0 && g.dist[ny][nx] == g.dist[cy][cx] - 1) { cx = nx; cy = ny; break; }
            }
            if (g.seen[cy][cx]) drawCircle(w, cx * TILE + 11.f, cy * TILE + 11.f, 3, Col(120, 255, 170, 190));
        }
    }

    // torch glow (additive light around the player)
    float flicker = 1 + 0.03f * sin(g.time * 9) + 0.02f * sin(g.time * 23);
    for (int i = 0; i < 6; i++) {
        float r = (4.6f - i * 0.6f) * TILE * flicker;
        sf::CircleShape glow(r, 48);
        glow.setOrigin({r, r});
        glow.setPosition({g.drawX * TILE + TILE / 2.f, g.drawY * TILE + TILE / 2.f});
        glow.setFillColor(Col(255, 170, 70, 7));
        w.draw(glow, sf::RenderStates(sf::BlendAdd));
    }

    for (auto& e : g.enemies)
        if (e.alive && g.visible(e.x, e.y)) drawEnemy(w, e, g.time);
    drawPlayer(w, g);

    for (auto& p : g.parts)                                                         // particles
        drawRect(w, p.x, p.y, p.size, p.size, withAlpha(p.color, p.life / p.maxLife));
    for (auto& f : g.floaters)                                                      // floating text
        drawTextC(w, f.text, f.x, f.y, 16, withAlpha(f.color, f.life * 1.5f));
}

// HUD
// Draws the small overview map: seen tiles, stairs (gold), monsters (red), hero (blinking green).
void drawMinimap(sf::RenderWindow& w, Game& g, float ox, float oy) {
    const float s = 6;
    for (int y = 0; y < MH; y++)
        for (int x = 0; x < MW; x++) {
            if (!g.seen[y][x]) continue;
            Col c = g.grid[y][x] == 1 ? Col(70, 62, 100) : (g.visible(x, y) ? Col(150, 145, 175) : Col(95, 90, 115));
            if (x == g.stairsX && y == g.stairsY) c = GOLD;
            drawRect(w, ox + x * s, oy + y * s, s, s, c);
        }
    for (auto& e : g.enemies)
        if (e.alive && g.visible(e.x, e.y)) drawRect(w, ox + e.x * s, oy + e.y * s, s, s, RED);
    if (int(g.time * 3) % 2 == 0) drawRect(w, ox + g.px * s - 1, oy + g.py * s - 1, s + 2, s + 2, GREEN);
}

// Draws the right sidebar: minimap, potion stack, nearby monsters (sorted), gear list, key help.
void drawSidebar(sf::RenderWindow& w, Game& g) {
    float x0 = float(MAP_W);
    drawRect(w, x0, 0, SIDE, float(MAP_H), Col(14, 12, 20));

    // minimap
    drawPanel(w, x0 + 2, 2, SIDE - 4, 164, "MINI MAP");
    drawMinimap(w, g, x0 + 7, 28);

    // potion bag: draw the stack from top to bottom
    drawPanel(w, x0 + 2, 170, SIDE - 4, 66, "POTION BAG (stack)");
    if (g.potions.empty()) drawText(w, "empty", x0 + 12, 202, 14, GREY);
    stack<int> copy = g.potions;
    for (int i = 0; !copy.empty() && i < 7; i++, copy.pop()) {
        float bx = x0 + 10 + i * 26.f;
        if (i == 0) drawRect(w, bx - 3, 195, 24, 34, withAlpha(GOLD, 0.35f));       // next potion
        drawRect(w, bx + 3, 202, 12, 14, Col(225, 55, 85));
        drawRect(w, bx + 6, 197, 6, 6, Col(190, 220, 240));
        drawText(w, to_string(copy.top()), bx, 215, 11, WHITE);
    }

    // nearby monsters, closest first
    drawPanel(w, x0 + 2, 240, SIDE - 4, 116, "NEARBY");
    vector<pair<int, int>> near;                                   // (distance, enemy index)
    for (int i = 0; i < (int)g.enemies.size(); i++)
        if (g.enemies[i].alive && g.visible(g.enemies[i].x, g.enemies[i].y))
            near.push_back({g.dist[g.enemies[i].y][g.enemies[i].x], i});
    sort(near.begin(), near.end());                                // [SORT] closest first
    if (near.empty()) drawText(w, "all quiet...", x0 + 12, 272, 14, GREY);
    for (int k = 0; k < (int)near.size() && k < 3; k++) {
        Enemy& e = g.enemies[near[k].second];
        float y = 266 + k * 29.f;
        drawRect(w, x0 + 10, y + 3, 10, 10, e.color);
        drawText(w, e.name, x0 + 25, y - 1, 13, e.color);
        drawText(w, to_string(near[k].first) + " away", x0 + 130, y - 1, 12, GREY);
        drawBar(w, x0 + 25, y + 14, 160, 6, float(e.hp) / e.maxHp, RED);
    }

    // gear: walk the linked list
    drawPanel(w, x0 + 2, 360, SIDE - 4, 92, "GEAR (linked list)");
    int n = 0;
    for (GearNode* gn = g.gear; gn && n < 4; gn = gn->next, n++) {
        drawText(w, gn->armor ? "[A]" : "[S]", x0 + 10, 386 + n * 16.f, 13, gn->armor ? CYAN : ORANGE);
        drawText(w, gn->name, x0 + 40, 386 + n * 16.f, 13, WHITE);
    }
    if (!g.gear) drawText(w, "nothing yet", x0 + 12, 388, 13, GREY);

    // keys
    drawPanel(w, x0 + 2, 456, SIDE - 4, 130, "KEYS");
    const char* keys[] = {"WASD/Arrows  move", "E            potion", "Space        wait", "Tab          route", "Esc          quit"};
    for (int i = 0; i < 5; i++) drawText(w, keys[i], x0 + 12, 484 + i * 19.f, 13, i == 3 && g.showPath ? GREEN : GREY);
}

// Draws the bottom area: hero stats/bars and the event log (copy of the message queue).
void drawBottomHud(sf::RenderWindow& w, Game& g) {
    float top = float(MAP_H);
    drawRect(w, 0, top, float(WIN_W), HUD, Col(14, 12, 20));

    // stats panel
    drawPanel(w, 2, top + 2, 350, HUD - 4, "HERO   Floor " + to_string(g.floorNo) + "   Level " + to_string(g.lvl));
    drawBar(w, 12, top + 30, 330, 18, float(g.hp) / g.maxHp, Col(215, 55, 70), "HP " + to_string(max(0, g.hp)) + " / " + to_string(g.maxHp));
    int lo = g.xpNeed[g.lvl - 1], hi = g.xpNeed[g.lvl];
    drawBar(w, 12, top + 54, 330, 13, float(g.xp - lo) / float(hi - lo), Col(70, 140, 250), "XP " + to_string(g.xp) + " / " + to_string(hi));
    drawText(w, "Gold " + to_string(g.gold), 12, top + 74, 15, GOLD);
    drawText(w, "Kills " + to_string(g.kills), 110, top + 74, 15, WHITE);
    drawText(w, "Score " + to_string(g.score()), 205, top + 74, 15, GREEN);
    drawText(w, "Attack +" + to_string(g.gearBonus(false)), 12, top + 96, 14, ORANGE);
    drawText(w, "Defense +" + to_string(g.gearBonus(true)), 110, top + 96, 14, CYAN);
    drawText(w, "Next turn: " + to_string(g.clockTime), 225, top + 96, 14, GREY);

    // message log panel (copy the queue so we can read it in order)
    drawPanel(w, 356, top + 2, WIN_W - 358, HUD - 4, "EVENT LOG (queue)");
    queue<Msg> copy = g.log;
    float y = top + 26;
    int total = (int)copy.size(), i = 0;
    while (!copy.empty()) {
        float a = 0.45f + 0.55f * (float(++i) / total);              // newest message is brightest
        drawText(w, copy.front().text, 366, y, 15, withAlpha(copy.front().color, a));
        copy.pop();
        y += 19;
    }
}

// Shows the fading 'FLOOR N' title when a new floor begins.
void drawBanner(sf::RenderWindow& w, Game& g) {
    if (g.banner <= 0) return;
    float a = min(1.f, g.banner);
    drawRect(w, 0, 215, float(MAP_W), 70, Col(0, 0, 0, (uint8_t)(150 * a)));
    drawTextC(w, "FLOOR " + to_string(g.floorNo), MAP_W / 2.f, 222, 44, withAlpha(GOLD, a));
}

// Draws the title screen: gradient background, embers, logo, instructions, best score.
void drawMenu(sf::RenderWindow& w, Game& g) {
    for (int i = 0; i < 12; i++)                                       // simple vertical gradient
        drawRect(w, 0, i * WIN_H / 12.f, float(WIN_W), WIN_H / 12.f + 1, Col(uint8_t(10 + i * 2), uint8_t(8 + i), uint8_t(22 + i * 3)));
    for (auto& p : g.parts) drawRect(w, p.x, p.y, p.size, p.size, withAlpha(p.color, p.life / p.maxLife));

    float cx = WIN_W / 2.f, pulse = 0.8f + 0.2f * sin(g.time * 2.5f);
    drawTextC(w, "DUNGEON", cx, 90, 78, shade(Col(220, 190, 90), pulse));
    drawTextC(w, "BOUND", cx, 165, 78, shade(Col(235, 90, 90), pulse));
    drawTextC(w, "descend. fight. survive.", cx, 258, 20, GREY);

    drawPanel(w, cx - 190, 310, 380, 190, "HOW TO PLAY");
    const char* lines[] = {"WASD / Arrows   move and attack", "E               drink a potion", "Space           wait a turn",
                           "Tab             show route to stairs", "Reach the stairs to go deeper!"};
    for (int i = 0; i < 5; i++) drawText(w, lines[i], cx - 175, 340 + i * 29.f, 16, i == 4 ? GOLD : WHITE);

    if (int(g.time * 2) % 2 == 0) drawTextC(w, "Press ENTER to start", cx, 540, 28, GREEN);
    vector<pair<int, int>> top;
    topScores(leaderboard, top, 1);
    if (!top.empty()) drawTextC(w, "Best score this session: " + to_string(top[0].first), cx, 600, 18, GOLD);
}

// Draws the death screen: score and the top-5 leaderboard read from the BST.
void drawGameOver(sf::RenderWindow& w, Game& g) {
    drawRect(w, 0, 0, float(WIN_W), float(WIN_H), Col(0, 0, 0, 190));
    float cx = WIN_W / 2.f;
    drawPanel(w, cx - 230, 90, 460, 520, "GAME OVER");
    drawTextC(w, "YOU DIED", cx, 120, 60, Col(225, 55, 65));
    drawTextC(w, "Floor " + to_string(g.floorNo) + "   Gold " + to_string(g.gold) + "   Kills " + to_string(g.kills), cx, 200, 20, WHITE);
    drawTextC(w, "Score: " + to_string(g.score()), cx, 235, 32, GOLD);

    drawTextC(w, "LEADERBOARD (binary search tree)", cx, 300, 20, CYAN);
    vector<pair<int, int>> top;
    topScores(leaderboard, top, 5);                                    // BST traversal
    for (size_t i = 0; i < top.size(); i++) {
        bool me = top[i].first == g.score() && top[i].second == g.floorNo;
        Col c = me ? GREEN : WHITE;
        drawText(w, to_string(i + 1) + ".", cx - 150, 340 + float(i) * 34, 22, c, true);
        drawText(w, to_string(top[i].first) + " pts", cx - 110, 340 + float(i) * 34, 22, c, true);
        drawText(w, "floor " + to_string(top[i].second), cx + 50, 340 + float(i) * 34, 22, GREY, true);
    }
    if (int(g.time * 2) % 2 == 0) drawTextC(w, "Press R to try again", cx, 550, 26, GREEN);
}


// Program entry: opens the window, then loops forever:
//   1) read keyboard events   2) update animations   3) draw the right screen for the current state
int main() {
    if (!font.openFromFile("C:/Windows/Fonts/arial.ttf") && !font.openFromFile("arial.ttf")) {
        cerr << "Could not load a font (arial.ttf).\n";
        return 1;
    }
    sf::RenderWindow window(sf::VideoMode({(unsigned)WIN_W, (unsigned)WIN_H}), "DungeonBound");
    window.setFramerateLimit(60);

    Game game;
    sf::Clock clock;

    while (window.isOpen()) {
        while (const optional<sf::Event> ev = window.pollEvent()) {
            if (ev->is<sf::Event::Closed>()) window.close();
            if (const auto* key = ev->getIf<sf::Event::KeyPressed>()) {
                using K = sf::Keyboard::Key;
                if (key->code == K::Escape) window.close();
                if (game.state == Game::State::Menu) {
                    if (key->code == K::Enter || key->code == K::Space) game.newGame();
                } else if (game.state == Game::State::Dead) {
                    if (key->code == K::R || key->code == K::Enter) game.newGame();
                } else {
                    switch (key->code) {
                        case K::W: case K::Up:    game.playerMove(0, -1); break;
                        case K::S: case K::Down:  game.playerMove(0, 1);  break;
                        case K::A: case K::Left:  game.playerMove(-1, 0); break;
                        case K::D: case K::Right: game.playerMove(1, 0);  break;
                        case K::E: game.usePotion(); break;
                        case K::Space: game.wait(); break;
                        case K::Tab: game.showPath = !game.showPath; break;
                        default: break;
                    }
                }
            }
        }
        game.update(min(clock.restart().asSeconds(), 0.05f));

        window.clear(Col(8, 6, 12));
        if (game.state == Game::State::Menu) {
            drawMenu(window, game);
        } else {
            // the world shakes when something hits; the HUD stays still
            sf::View view(sf::Vector2f(WIN_W / 2.f, WIN_H / 2.f), sf::Vector2f((float)WIN_W, (float)WIN_H));
            if (game.shake > 0) view.move({rndf() * game.shake, rndf() * game.shake});
            window.setView(view);
            drawWorld(window, game);
            window.setView(window.getDefaultView());

            drawBanner(window, game);
            if (game.flash > 0)                                              // red flash when hurt
                drawRect(window, 0, 0, float(MAP_W), float(MAP_H), Col(255, 0, 0, (uint8_t)(game.flash * 110)));
            drawSidebar(window, game);
            drawBottomHud(window, game);
            if (game.state == Game::State::Dead) drawGameOver(window, game);
        }
        window.display();
    }
    freeTree(leaderboard);
    return 0;
}