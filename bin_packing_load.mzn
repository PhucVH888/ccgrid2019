include "globals.mzn";

%%%%%%%%%%%%%%%%%%%%%%%%%
% PARAMETERS
%%%%%%%%%%%%%%%%%%%%%%%%%
int: V;% (1 .. 10.000) the number of videos
int: E;% (1 .. 1.000) the number of endpoints
int: R;% (1 .. 1.000.000) the number of request descriptions
int: C;% (1 .. 1.000) the number of cache servers
int: X;% (1 .. 500.000) the capacity of each cache server in MB

set of int: VID      = 1..V;
set of int: ENDPOINT = 1..E;
set of int: CACHE    = 1..C;
set of int: CACHE0   = 0..C;
set of int: CAP0     = 0..X;
set of int: SIZE     = 1..1000;
set of int: SIZE0    = 0..1000;

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
array[RREQ, RVEN] of int: request;

% number of distinct request
int: realReq; 
set of int: RREQ = 1..realReq;

% ei: from endpoint 
% ci: to cache ( 0 .. C ), 
% Lc: latency  ( 1 .. 500 < Ld ) in milliseconds
% eConCache[en, ca] : 
%    Lc: connects to cache id; 
%    0 : not connect
array[ENDPOINT, CACHE] of 0..1000: eConCache;

% total number of requests: 
% int: nReq = sum(re in RREQ)(request[ re, Rn ]);

% valid requested videos
int: nReqVid;
array[VID] of SIZE0: reqVid;
array[VID] of SIZE0: videoInCap;

%%%%%%%%%%%%%%%%%%%%%%%%%
% VARIABLES
%%%%%%%%%%%%%%%%%%%%%%%%%
array[VID] of var CACHE0: bin;
array[VID] of var CAP0: load;
var int: savingTime;

%%%%%%%%%%%%%%%%%%%%%%%%%
% CONSTRAINTS
%%%%%%%%%%%%%%%%%%%%%%%%%
constraint bin_packing_load(load, bin, reqVid);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SYMMETRY BREAKING CONSTRAINTS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% % symmetry breaking: 
% constraint symmetry_breaking_constraint(forall(ca in 1..C-1) (
%        (load[ca + 1] > 0 -> load[ca] > 0)
%        /\ % and should be filled in order of weight
%        (load[ca] >= load[ca + 1]) 
% ));

% % symmetry breaking: use domain consistency for this constraint
% constraint symmetry_breaking_constraint(decreasing(load) :: domain);

% % another symmetry breaking: first bin must be loaded
% constraint symmetry_breaking_constraint(load[1] > 0);

%%%%%%%%%%%%%%%%%%%%%%%%%
% Objective Function
%%%%%%%%%%%%%%%%%%%%%%%%%
savingTime = sum(req in RREQ where request[req, Rn] > 0)(
  let { int: rv = request[req, Rv]; % requested video
        int: re = request[req, Re]; % requested endpoint
        int: rn = request[req, Rn]; % number of requests
        int: ld = endpoint[re, Ld]; % latency of data center to endpoint
        var int: lc = eConCache[re, bin[request[req, Rv]]];% latency of cache to endpoint
   } in (
      (ld - lc) % saving time when storing in cache
      *            
      (bool2int(videoInCap[rv] > 0)) % size=0: stored in data center, saving 0 ms
      *  
      rn % number of requests for video rv
));

solve :: int_search(
        bin ++ load, 
        first_fail, indomain_min, complete) 
        maximize savingTime;


%%%%%%%%%%%%%%%%%%%%%%%%%
% Output
%%%%%%%%%%%%%%%%%%%%%%%%%
output [show((savingTime/nReq)*1000) ++ "\n" ++
        show(sum(vi in VID)(bool2int(load[vi] > 0)))] ++
       [ if vi = 1 then "\n\(b) " else "" endif ++
         if (fix(reqVid[vi]) > 0 /\ fix(bin[vi]) = b) 
         then "\(vi) "
         else "" endif 
         | b in CACHE, vi in VID];

% for test server
var int: nReq; nReq = sum(re in RREQ)(request[ re, Rn ]);

% output ["\nbin = " ++ show(bin) ++ "\nload = " ++ show(load)];      