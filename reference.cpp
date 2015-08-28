#include <bits/stdc++.h>
#define f(x,n) for(int x=0;x<n;x++)
#define INF 1<<30

using namespace std;

typedef int num;
typedef vector<num> vi;
typedef vector< vi > vvi;
typedef vector<ii> vii;
typedef stack<num> si;
typedef queue<num> qi;
typedef pair<num,num> ii;




/************************************************************************** Data Structures ************************************************************/

#define lsb(x) x&(-x)

struct Fenwick{
	vi b;
	Fenwick(int n): b(n+1,0) {}
	void update(int i,num v){ for(;i<b.size();i+=lsb(i) ) b[i]+=v; }
	num query(int i){ num m=0;  for(;i!=0;i-=lsb(i) ) m+=b[i]; return m;}
};

void r_update(Fenwick b1,Fenwick b2,int i,int j,num v){ b1.update(i,v); b1.update(j+1,-v); b2.update(i,v*(i-1)); b2.update(j+1,-v*j); }
num r_query(Fenwick b1,Fenwick b2,int i){ return b1.query(i)*i - b2.query(i); }

struct Fenwick2D{
	vvi b;
	Fenwick2D(int l,int h): b(l+1, vi(h+1,0) ) {}
	void update(int x, int y, num v){ for(int i=x;i<b.size();i+=lsb(i)) for(int j=y;j<b[i].size();j+=lsb(j)) b[i][j]+=v; }
	num query(int x,int y){ num m=0; for(int i=x;i!=0;i-=lsb(i)) for(int j=y;j!=0;j-=lsb(j)) m+=b[i][j]; return m;}
	num query(int x1,int y1,int x2,int y2){  return query(x2,y2) + query(x1-1,y1-1) - query(x1-1,y2) - query(x2,y1-1); }
};


#define NEUTRO 0

struct SegmentTree{
	num L,R,val,*lazy;
	SegmentTree *left,*right;

	SegmentTree(num  l,num r){	L=l; R=r;	val=NEUTRO;	lazy=NULL; left=right=NULL;}
	~SegmentTree(){ if(left) delete left; if(right) delete right; }

	num link(num a,num b){return a+b;}
	num range(num range,num val){ return range*val ;}
	num mix(num a,num b){return a+b;}

	void build(){
		if(left==NULL){	left=new SegmentTree( L, (L+R)/2 );	right=new SegmentTree( (L+R)/2 +1, R);	}
		if(lazy!=NULL){
			left->update(L, (L+R)/2 ,*lazy);	right->update( (L+R)/2 +1 , R ,*lazy);
			delete lazy;	lazy=NULL;
	}	}

	void update(num i,num j,num v){
		if( i>R || j<L ) return;
		if( L>=i && R<=j ){  val=mix(val, range(R-L+1,v) ); if(lazy==NULL){lazy=new num; *lazy=NEUTRO;} *lazy=mix(*lazy,v); return;}  
		build();	left->update(i,j,v);	right->update(i,j,v);
		val = link( left->val, right->val );	}

	num  query(num i,num j){
		if( i>R || j<L ) return NEUTRO;	if( L>=i && R<=j ) return val;
		build();	return link( left->query(i,j) , right->query(i,j) );	}
};


struct UnionFind{
	int sets;	vi p,l;
	UnionFind(int n){ sets=0; f(i,n) make(); }
	void make(){ p.push_back(p.size()); l.push_back(1); sets++; }
	int find(int u){if(u!=p[u]) p[u]=find(p[u]); return p[u];}
	void join(int u,int v){	u=find(u); v=find(v); if(u!=v){ p[v]=u; l[u]+=l[v]; sets--; } }
};




/************************************************************************** Geometry 2D ****************************************************************/

#define EPS 1e-9

bool equal(double a,double b){return fabs(b-a)<EPS;}

struct Point{
	double x,y;
	Point(double x_,double y_): x(x_), y(y_) {}
	Point operator-(Point p){ return Point(x-p.x,y-p.y); }
	double operator*(Point p){ return x*p.y-y*p.x;}
	double operator~(){ return hypot(x,y);}
	Point operator*(double s){ return Point(s*x,s*y);}
	bool operator==(const Point &p) const { return equal(x,p.x) && equal(y,p.y); }
	bool operator<(const Point &p) const { return   !equal(x,p.x)? x<p.x : equal(y,p.y)? false: y<p.y;}
	Point operator+(Point p){ return Point(x+p.x,y+p.y);}
	double operator%(Point p){return x*p.x+y*p.y;}	
	Point rot(double arc){ return Point(x*cos(arc)-y*sin(arc), x*sin(arc)+y*cos(arc) );}
};


double arc(Point &p,Point &q){ return acos( (p%q)/(~p * ~q) );}

struct Line{
	Point m,d;
	Line(Point &p,Point &q): m(p-q), d(p) {}
	bool operator==(Line &l){ return equal(m*l.m,0) && equal( (d-l.d)*m,0) ;}
	double distance(Point &p){ return fabs( (d-p)*m ) / ~m ;}
	int intersect(Line &l){ return  equal(m*l.m,0) ?  ( equal( (d-l.d)*m, 0) ? INF: 0 )  : 1;  }
	Point intersection(Line &l){return  d - m*(  l.m*(d-l.d)/(l.m*m)  ) ;}
	double distance(Line &l){return equal(m*l.m,0)? distance(l.d): 0 ; }
};




/****************************************************************************** Graph ************************************************************************/
typedef int key;

struct Graph{
	int n;
	map<key,int> t1;
	vector<key> t2;

	vvi cons;
	vvi wei;
	vi in_degs;
	vector< set<int> > reps;
	
	Graph(): n(0) {}
	Graph(int nodes) : n(nodes), cons( nodes,vi() ), wei( nodes,vi() ), in_degs(nodes,0), reps(nodes, set<int>() ) {}


	void add_node(key u){
		if(t1.count(u)==0){ 
			t1[u]=n++;	t2.push_back(u);
			cons.push_back( vi() );
			wei.push_back( vi() ); 
			in_degs.push_back(0); 
			reps.push_back( set<int>() );
	}	}


	void add_edge(key u,key v,int w){
		add_node(u); add_node(v);
		int a=t1[u],b=t1[v];
		if(reps[a].count(b)) return;
		cons[a].push_back(b);
		wei[a].push_back(w);
		in_degs[b]++;
		reps[a].insert(b);	}


	int edge_distance(int u,vi &dist){
		int v,nodes=0;	qi order;	dist[u]=0;	order.push(u);
		while(!order.empty()){
			u=order.front();	order.pop();	nodes++;
			f(i,cons[u].size()){
				v=cons[u][i];	if(dist[v]==INF){ order.push(v);	dist[v]=dist[u]+1; }
	}	}return nodes; }


	void topo_sort(vi &topo){
		qi order;	int u,v; vi in_degs(this->in_degs);
		f(i,n)	if(!in_degs[i]) order.push(i);
		while(!order.empty()){
			u=order.front(); order.pop();	topo.push_back(u);
			f(i,cons[u].size()){
				v=cons[u][i];	if( !(--in_degs[v]) ) order.push(v);	}
	}	}

	bool bicolor(int u,vi &color){
		int v; 	qi order;	color[u]=0;	order.push(u);
		while(!order.empty()){
			u=order.front(); order.pop();
			f(i,cons[u].size()){
				v=cons[u][i];
				if(color[v]==INF){	color[v]=1-color[u];	order.push(v);	}
				else if(color[v]==color[u]) return false;	
	}	} return true; }


};




int  grid_edge_distance(vvi &grid, vvi &dist, int r,int c){
	int dr[]={1,1,0,-1,-1,-1,0,1};	int dc[]={0,1,1,1,0,-1,-1,-1};
	int nodes=0,rr,cc;	queue< ii > order;
	if(grid[r][c]==1){	dist[r][c]=0;	order.push( ii(r,c) );	}
	while(!order.empty()){
		r=order.front().first;	c=order.front().second;	order.pop(); nodes++;
		f(i,8){
			rr=r+dr[i]; 	cc=c+dc[i];
			if(rr>=0 && cc>=0  && grid[rr][cc]==1 && dist[rr][cc]==INF )
				{	dist[rr][cc]=dist[r][c]+1;	order.push( ii(rr,cc) );	}
	}	}	return nodes; }








int main(){

	return 0;
}



//  cls && g++ reference.cpp -o reference