#include <iostream>
#include <sstream>
#include <algorithm>
#include <memory>
#include "minisat/core/Solver.h"
#include <vector>
#include <set>
#include <list>
#include <time.h>
#include <errno.h>
using namespace std;

unsigned int n,n_edges;
string str;
struct Edge{
    unsigned v1,v2;
};

typedef std::vector<unsigned> VertexVec;
typedef std::list<unsigned > VertexList;
typedef std::vector<VertexList> AdjacencyList;
typedef std::vector<VertexList> VertexCover;
vector<unsigned int> outputE_copy;
vector<unsigned int> outputV;

struct Graph{

    AdjacencyList adjacency;
    VertexCover vertex_cover;
    void init(unsigned num_vertices);
    void add(Edge e);
    void clear(unsigned v);
};

void vsplit()
{
    outputV.clear();
    outputE_copy.clear();

    std::vector<std::string> a;
     std::size_t prev_pos = 0, pos;
         while ((pos = str.find_first_of(" ", prev_pos)) != std::string::npos)
         {
            if (pos > prev_pos)
              a.push_back(str.substr(prev_pos, pos-prev_pos));
            prev_pos= pos+1;
         }
        if (prev_pos< str.length())
            a.push_back(str.substr(prev_pos, std::string::npos));





for (auto &s : a) {
    std::stringstream parser(s);
    unsigned int x = 0;

    parser >> x;

    outputV.push_back(x);
}
n=outputV[1];

}


void Source_Dest(Graph &gp)
{
    gp.init(n);

    unsigned int u,v;
    for(unsigned int j=1; j<outputE_copy.size(); j=j+2)
       {
           u=outputE_copy[j-1];
           v=outputE_copy[j];
           gp.add({u,v});


       }
}

/*void timeCalculate()
{
clockid_t clk_id;
    struct timespec tspec;
    pthread_t tid;
    tid = pthread_self();
    if (pthread_getcpuclockid( tid, &clk_id) == 0)
    {
        if (clock_gettime( clk_id, &tspec ) != 0)
        {
            perror ("clock_gettime():");
        }
        else
        {
           printf ("%d,%ld\n",
                     tspec.tv_sec, tspec.tv_nsec);
        }
    }
    else
    {
        printf ("pthread_getcpuclockid(): no thread with ID %d.\n", tid);
    }
}*/
void * Vertex_Cover(void *input)
{
   // cout<<"hi1"<<endl;
Graph graph_input = *(const Graph *)input;
VertexVec &C = *new VertexVec();


    unsigned int high = graph_input.adjacency.size();
    unsigned int low = 0;
    unsigned int k = 0;
    bool res;
    k=(low+high)/2;
    while (low <= high)
    {
         std::unique_ptr<Minisat::Solver> solver(new Minisat::Solver());


        std::vector<std::vector<Minisat::Lit>> nk_matrix(graph_input.adjacency.size());
        for (unsigned int i = 0; i < graph_input.adjacency.size(); i++)
            for (unsigned int j = 0; j < k; j++) {
                Minisat::Lit l = Minisat::mkLit(solver->newVar());
                nk_matrix[i].push_back(l);
            }
        // first condition
        for (unsigned int i = 0; i < k; i++) {
            Minisat::vec<Minisat::Lit> save_literal;
            for (unsigned int j = 0; j < graph_input.adjacency.size(); j++) {
                save_literal.push(nk_matrix[j][i]);
            }
            solver->addClause(save_literal);
        }

// second condition
        for (unsigned int m = 0; m < graph_input.adjacency.size(); m++)
            for (unsigned int p = 0; p < k; p++)
                for (unsigned int q = p + 1; q < k; q++) {
                    solver->addClause(~nk_matrix[m][p], ~nk_matrix[m][q]);
                }
//third condition
        for (unsigned int m = 0; m < k; m++)
            for (unsigned int p = 0; p < graph_input.adjacency.size(); p++)
                for (unsigned int q = p + 1; q < graph_input.adjacency.size(); q++) {
                    solver->addClause(~nk_matrix[p][m], ~nk_matrix[q][m]);
                }


//forth condition
        for(unsigned v1 = 0 ; v1 < graph_input.adjacency.size(); ++v1) {
            for (auto v2 : graph_input.adjacency[v1]) {
                if(v2 < v1) continue;
                Minisat::vec<Minisat::Lit> edge_lit;
                for (unsigned int w = 0; w < k; w++) {
                    edge_lit.push(nk_matrix[v1][w]);
                    edge_lit.push(nk_matrix[v2][w]);
                }

                solver->addClause(edge_lit);
            }
        }
        res = solver->solve();
        if (res )
        {   C.clear();
            for ( unsigned int i = 0; i < graph_input.adjacency.size(); i++)
                for ( unsigned int j =0; j < k; j++)

                    if ( Minisat::toInt(solver->modelValue(nk_matrix[i][j])) == 0)
                    {
                        C.push_back(i);
                    }

            high=k-1;
        }
        else {
            solver.reset(new Minisat::Solver());
            low=k+1;
        }
        k=(low+high)/2;
    }
    cout<<"CNF-SAT-VC: ";
    std::sort( C.begin(), C.end(), std::less<int>());
   for (unsigned j=0; j < C.size(); j++){
            std::cout<<C[j];
            if(j + 1 != C.size()){
                std::cout<<',';
            }
        }
        std::cout<<std::endl;

//timeCalculate();
return nullptr;
}


void * APPROX_VC2(void *input)
{
   // cout<<"Hi2"<<endl;
    Graph graph_input = *(const Graph *)input;
    bool visited[n];
    vector <unsigned int> C;
   // unsigned int c=0;
    for (unsigned int i=0; i<n; i++)
        visited[i] = false;

    list<unsigned int>::iterator i;

    // Consider all edges one by one
    for (unsigned int u=0; u<n; u++)
    {
        // An edge is only picked when both visited[u] and visited[v]
        // are false
        if (visited[u] == false)
        {
            // Go through all adjacents of u and pick the first not
            // yet visited vertex (We are basically picking an edge
            // (u, v) from remaining edges.
            for (i= graph_input.adjacency[u].begin(); i != graph_input.adjacency[u].end(); ++i)
            //for (i= graph_input.adjacency[u].begin(); i != graph_input.adjacency[u].end(); ++i)

            {
                int v = *i;
                if (visited[v] == false)
                {
                     // Add the vertices (u, v) to the result set.
                     // We make the vertex u and v visited so that
                     // all edges from/to them would be ignored
                     visited[v] = true;
                     visited[u]  = true;
                        //c++;
                     break;
                }
            }
        }
    }

    // Print the vertex cover
    for (unsigned int j=0; j< n; j++)
    {
         if (visited[j])
        C.push_back(j);
    }
   cout<<"APPROX_VC2: ";
    for (unsigned int i=0; i<C.size(); i++)
    {

            cout <<C[i];

           // cout<<n;

        if(i + 1 != C.size()){
                std::cout<<',';
            }


    }
//timeCalculate();
     std::cout<<std::endl;
    return nullptr;
}

void * APPROX_VC1(void *input)
{
//cout<<"Hi3"<<endl;
Graph graph_input = *(const Graph *)input;
VertexVec &C = *new VertexVec();
n_edges=outputE_copy.size()/2;
while(n_edges>0)
{
     auto v = std::max_element(
                graph_input.adjacency.begin(),graph_input.adjacency.end(),
                [](VertexList &list1, VertexList &list2)->bool{ return list1.size()<list2.size(); } //?
        );
    unsigned i = (unsigned)(v-graph_input.adjacency.begin());
    C.push_back(i);
    graph_input.clear(i);


}

std::sort( C.begin(), C.end(), std::less<int>());
    std::cout<<"APPROX-VC-1: ";
   for(unsigned int g=0; g < C.size(); g++)
   {
        std::cout<< C[g];
       if(g + 1 != C.size()){
                std::cout<<',';
   }
   }
    std::cout<<std::endl;
    return &C;
//timeCalculate();
}
void algoThread(Graph &graph)
{
    Graph &graph_input = graph;
    pthread_t thread1;
    pthread_t thread2;
    pthread_t thread3;
    pthread_create(&thread3,NULL,Vertex_Cover,&graph_input);
    pthread_join(thread3,NULL);
    pthread_create(&thread1,NULL,APPROX_VC1,&graph_input);
    pthread_join(thread1,NULL);
    pthread_create(&thread2,NULL,APPROX_VC2,&graph_input);
    pthread_join(thread2,NULL);


}
void Esplit()
{
    Graph &graph_input = *new Graph();
    //adjaceny_matrix.clear();
    vector<string> b;
     std::size_t prev_pos = 0, pos;
         while ((pos = str.find_first_of("{<,>}", prev_pos)) != std::string::npos)
         {
            if (pos > prev_pos)
              b.push_back(str.substr(prev_pos, pos-prev_pos));
            prev_pos= pos+1;
         }
        if (prev_pos< str.length())
            b.push_back(str.substr(prev_pos, std::string::npos));
    vector<unsigned int> outputE;



    for (auto &s : b) {

        std::stringstream parser(s);
        unsigned int x = 0;

        parser >> x;

    outputE.push_back(x);
}

unsigned int check=0;
   for (unsigned int i=1; i<outputE.size(); i++)
   {
        if(outputE[i]>=0 && outputE[i]<n)
        {
            outputE_copy.push_back(outputE[i]);
        }
       else{
        check=1;
       }
   }

if(check==1)
{
    cout<<"Error: Edges out of range"<<endl;
}

 Source_Dest(graph_input);

algoThread(graph_input);


}


void Graph::init(unsigned n){
    adjacency.clear();
    //num_edges = 0;
    adjacency.resize(n,{});
}

void Graph::add(Edge e) {
    auto &list1 = adjacency[e.v1];
    auto &list2 = adjacency[e.v2];
    list1.push_back(e.v2);
    list2.push_back(e.v1);
    //num_edges ++;
}

void Graph::clear(unsigned v){

    if(v >= adjacency.size()) return;
    for(auto u : adjacency[v]){
        auto &list2 = adjacency[u];
        auto i2 = std::find(list2.begin(),list2.end(),v);
        if(i2 != list2.end()){
            list2.erase(i2);
            --n_edges;
        }
    }
    adjacency[v].clear();
}

void * GraphInput(void * input)
{
    while(getline(cin,str))

    {

                if(str[0]=='v' || str[0]=='V')
                {
                    vsplit();

                }
                else if(str[0]=='e' || str[0]=='E')
                {

                    Esplit();


                }


    }
    return nullptr;

}

int main(int argc, char **argv)
{

pthread_t thread;

    pthread_create(&thread,NULL,GraphInput,NULL);
    pthread_join(thread,NULL);

    return 0;
}
