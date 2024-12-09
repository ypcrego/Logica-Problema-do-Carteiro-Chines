package problema.carteiro.chines;

import problema.carteiro.chines.Vertice;

// import org.checkerframework.checker.units.qual.A;

import java.util.*;

public class Grafo {
    private int V = 0; // Número de vértices
    //@ spec_public
    private int L = 0; // Número de arestas
    //@ spec_public
    private List<Vertice> listaVertices = new ArrayList<Vertice>();

    //@ public invariant listaVertices != null;
    //@ ensures listaVertices != null;

    //@ pure
    public Grafo() {
        listaVertices = new ArrayList<Vertice>();
    }

    /**
     * Função para adicionar um vértice no grafo.
     * 
     * @param v Vértice a ser adicionado
     */
    void addVertice(int v) {
        Vertice aux = new Vertice(v);
        if (!listaVertices.contains(aux))
            listaVertices.add(aux);
        this.V++;
    }

    /**
     * Função para adicionar uma aresta de 2 vértices.
     * 
     * @param v1 Vértice 1
     * @param v2 Vértice 2
     */

    //@ normal_behaviour
    //@     requires v1 >= 0;
    //@     requires v2 >= 0;
    //@     requires listaVertices != null;
    //@     requires listaVertices.size() > 0;
    //@     requires L <= Integer.MAX_VALUE;
    //@     requires verticeExiste(v1) && verticeExiste(v2);
    //@     assigns L;
    //@     ensures L == \old(L) + 1;
    //@ also exceptional_behaviour
    //@     requires v1 >= 0;
    //@     requires v2 >= 0;
    //@     requires listaVertices != null;
    //@     requires listaVertices.size() > 0;
    //@     requires L <= Integer.MAX_VALUE;
    //@     requires !verticeExiste(v1) || !verticeExiste(v2);
    //@     assigns \nothing;
    //@     signals (IllegalArgumentException);
    //@     signals (NullPointerException);
    //@     signals (IndexOutOfBoundsException);
    //@     signals (UnsupportedOperationException);
    void addAresta(int v1, int v2) {
        if (!verticeExiste(v1) || !verticeExiste(v2)){
            throw new IllegalArgumentException("O vértice v1 não existe");
        }

        Vertice auxv1 = new Vertice(v1);
        Vertice auxv2 = new Vertice(v2);
        int index1 = listaVertices.indexOf(auxv1);
        int index2 = listaVertices.indexOf(auxv2);

        //@ requires index1 >= 0;
        //@ requires index1 < listaVertices.size();
        //@ requires index2 >= 0;
        //@ requires index2 < listaVertices.size();
        //@ requires listaVertices.get(index1) != null;
        //@ requires listaVertices.get(index2) != null;
        listaVertices.get(index1).listaAdjascencia.add(v2);
        listaVertices.get(index2).listaAdjascencia.add(v1);
        this.L++;
    }

    //@ pure
    Boolean verticeExiste(int n) {
        for (Vertice ver : listaVertices){
            if(ver.getN() == n){
                return true;
            }
        }
        return false;
    }

    /**
     * Função para remover uma aresta de 2 vértices.
     * 
     * @param v1 Vértice 1
     * @param v2 Vértice 2
     */
    void remAresta(int v1, int v2) {
        Vertice auxv1 = new Vertice(v1);
        Vertice auxv2 = new Vertice(v2);
        try {
            listaVertices.get(listaVertices.indexOf(auxv1)).listaAdjascencia.remove(new Integer(v2));
            listaVertices.get(listaVertices.indexOf(auxv2)).listaAdjascencia.remove(new Integer(v1));
        } catch (NullPointerException e) {
            e.printStackTrace();
            System.out.println("O vértice não existe");
        }
        this.L--;
    }

    //@ pure
    public void printGrafo() {
        for (Vertice ver : this.listaVertices) {
            System.out.print(ver.getN() + ": ");
            for (Integer adjver : ver.listaAdjascencia) {
                System.out.print(adjver + " ");
            }
            System.out.println();
        }
    }

    //@ pure
    public void printVertices() {
        for (Vertice ver : this.listaVertices) {
            System.out.print("(n: " + ver.getN() + " d: " + ver.getD() + " rot: " + ver.getRot() + ") \n");
        }
    }

    // Getters e Setters

    //@ pure
    public int getV() {
        return V;
    }

    public void setV(int v) {
        V = v;
    }

    //@ pure
    public int getL() {
        return L;
    }

    public void setL(int l) {
        L = l;
    }

    //@ pure
    public List<Vertice> getListaVertices() {
        return listaVertices;
    }

    //@ requires lista != null;
    //@ ensures this.listaVertices == lista;
    //@ ensures this.listaVertices.size() == lista.size();
    //@ ensures this.listaVertices != null;
    public void setListaVertices(List<Vertice> lista) {
        if (lista == null) {
            throw new IllegalArgumentException("Lista não pode ser nula!");
        }
        this.listaVertices = lista;
    }
}