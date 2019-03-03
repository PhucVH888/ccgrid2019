int: v;% (1 .. 10.000) the number of videos
int: e;% (1 .. 1.000) the number of endpoints
int: r;% (1 .. 1.000.000) the number of request descriptions
int: c;% (1 .. 1.000) the number of cache servers
int: x;% (1 .. 500.000) the capacity of each cache server in MB

set of int: VID  = 1..v;
set of int: VID0 = 0..v-1;

set of int: ENDPOINT = 1..e;
set of int: REQUEST = 1..r;

set of int: CACHE  = 1..c;
set of int: CACHE0 = 0..c;

set of int: CAPACITY = 1..x;
set of int: SIZE = 1..1000;

% sum of all connected caches K
int: total_connection; 

set of int: CONN = 1..total_connection;

% video sizes
array[VID] of SIZE: videoSize;

% Ld: data center latency       ( 2 .. 4.000 )
% K: number of connected caches ( 0 .. C )
enum LDK = {Ld, K};
array[ENDPOINT, LDK] of 0..4000: endpoint;

% Rv: requested video      ( 0 .. V )
% Re: coming from endpoint ( 0 .. E )
% Rn: number of requests   ( 0 .. 10.000)
enum RVEN = {Rv, Re, Rn};
array[REQUEST, RVEN] of 0..10000: request;

% number of cache servers ( 0 .. C : 1.000)
var CACHE0: n; 

% ei: from endpoint 
% ci: to cache ( 0 .. C ), 
% Lc: latency  ( 1 .. 500 < Ld ) in milliseconds
% eConCache[en, ca] : 
%    Lc: connects to cache id; 
%    0 : not connect
array[ENDPOINT, CACHE] of 0..1000: eConCache;

% 1: stored in data center
% 0: not in dc
array[ENDPOINT, VID] of var {0,1}: vInDc; 

% ci : id of cache server being described 
%      ( 0 .. C : 1.000 ), 0 : data center
% vi : id of videos stored in this cache server 
%      ( 0 .. V : 10.000 )
array[CACHE, VID] of var {0,1} : usedCache;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TASK
%   - decide which videos to put in which cache server
%   - minimize average waiting time for all requests
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% P1: Precomputation: number of used caches
constraint n = sum(ca in CACHE)(
    bool2int(exists(vi in VID)(usedCache[ca, vi] = 1))
);

% C1: Channelling constraint: Mark which videos stored in data center
constraint forall(req in REQUEST)(
  let { int: rv = request[req, Rv]; 
        int: re = request[req, Re]; 
  } in ((videoSize[rv] > x \/ endpoint[re, K] = 0) 
  <-> vInDc[re, rv] = 1 )
);


% C2: Sum of all video sizes per endpoint <= cache's capacity
constraint forall(ca in CACHE)(
    sum(vi in VID)(usedCache[ca, vi] * videoSize[vi]) 
    <= x
);


% C3: compute the saving time per request
var int: savingTime = sum(req in REQUEST, ca in CACHE)(
  let { int: rv = request[req, Rv]; % requested video
        int: re = request[req, Re]; % requested endpoint
        int: rn = request[req, Rn]; % number of requests
        int: ld = endpoint[re, Ld]; % latency of data center to endpoint
        int: lc = eConCache[re, ca];% latency of cache to endpoint
   } in (
      (ld - lc) *            % saving time when storing in cache ca
      (1 - vInDc[re, rv]) *  % saving 0 ms if storing in data center
      rn *                   % number of requests for video rv
      usedCache[ca, rv]      % 1: is video rv is stored in cache ca; 
                             % 0: otherwise
));


% P2: pre-computation: total number of all requests
var int: nReq;
constraint nReq = sum(re in REQUEST)(request[ re, Rn ]);
% F1: returns 0 if the video is not stored in any other caches 
%     except cach ca
function var int: selectedVideo(int: ca, int: rv) = 
    sum(c1 in CACHE where c1 != ca)(
        bool2int(usedCache[c1, rv] = 1));

% F2: check capacity of cache ca if storing video vi
function var bool: hungryCache(int: ca, int: vi) = 
    x >= 
    (sum(vvi in VID)(videoSize[vvi] * usedCache[ca, vi]) 
     + videoSize[vi]
    );

% F3: check if cache ca is empty
function var bool: emptyCache(int: ca) = 
    sum(vi in VID)(usedCache[ca, vi]) = 0;

% C4: pre-computation predicted requests: unrequested videos 
%     will be stored
constraint forall(en in ENDPOINT, ca in CACHE, vi in VID )(
    eConCache[ en, ca ] > 0 /\ vInDc[ en, vi ] = 0 /\ 
    emptyCache(ca) /\ hungryCache(ca, vi)
    -> usedCache[ ca, vi ] = 1
);


% C5: store the requested videos iff there is still room in each cache
constraint forall(en in ENDPOINT, ca in CACHE, vi in VID)(
    eConCache[ en, ca ] > 0 /\ vInDc[ en, vi ] = 0 /\ 
    selectedVideo(ca, vi) = 0
    -> usedCache[ ca, vi ] = 1
);

% C6: Avoid duplication
include "at_most.mzn";
constraint forall(vi in VID)(
    at_most(1, [ usedCache[ ca, vi] | ca in CACHE ], 1)
);

% Decision variable: total time that saved for all requests
%     nReq is parameter, the division and multiplication 
%     could be performed at the output phase.
% score = (savingTime / nReq ) * 1000
var int: score;
constraint score = savingTime;
solve maximize score;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Output for test server
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
output [  %"V: " ++ show(v) ++ "\n" ++
%           "C: " ++ show(c) ++ "\n" ++
%           "E: " ++ show(e) ++ "\n" ++
%           "R: " ++ show(r) ++ "\n" ++
          "S: \(score/nReq)" ++ "\n"];

% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% % Output to file
% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% output ["\(n)"] ++
%        [ if j = 1 then "\n\(i-1) " % cacheId
%          else "" endif ++ 
%          if fix(usedCache[i, j]) > 0 /\ 
%             j >= 1 then "\(j-1) "  % videoId
%          else "" endif 
%          | i in CACHE, j in VID] ++
%        ["\nscore: \((score/nReq)*1000)" 
% %        ++"\n" ++ show2d(usedCache)
%        ];

output  ["\n score: \((score/nReq)*1000)"];
