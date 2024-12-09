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
    //@ public invariant \forall int i; 0 <= i < listaVertices.size(); listaVertices.get(i) != null;
    //@ ensures listaVertices != null;
    //@ ensures \forall int i; 0 <= i < listaVertices.size(); listaVertices.get(i) != null;

    //@ pure
    public Grafo() {
        listaVertices = new ArrayList<Vertice>();
    }

    /**
     * Função para adicionar um vértice no grafo.
     * 
     * @param v Vértice a ser adicionado
     */
    //@ requires v >= 0;
    //@ requires \forall int i; 0 <= i < listaVertices.size(); listaVertices.get(i) != null;
    //@ ensures \forall int i; 0 <= i < listaVertices.size(); listaVertices.get(i) != null;
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

    //@ normal_behavior
    //@     requires v1 >= 0;
    //@     requires v2 >= 0;
    //@     requires listaVertices != null;
    //@     requires listaVertices.size() > 0;
    //@     requires \forall int i; 0 <= i < listaVertices.size(); listaVertices.get(i) != null;
    //@     requires L <= Integer.MAX_VALUE;
    //@     requires verticeExiste(v1) && verticeExiste(v2);
    //@     assigns L;
    // @     ensures L == \old(L) + 1;
    //@ also exceptional_behavior
    //@     requires v1 >= 0;
    //@     requires v2 >= 0;
    //@     requires listaVertices != null;
    //@     requires listaVertices.size() > 0;
    //@     requires \forall int i; 0 <= i < listaVertices.size(); listaVertices.get(i) != null;
    //@     requires L <= Integer.MAX_VALUE;
    //@     requires !verticeExiste(v1) || !verticeExiste(v2);
    //@     assigns \nothing;
    //@     signals_only IllegalArgumentException, NullPointerException, RuntimeException;
    void addAresta(int v1, int v2) {
        if (!verticeExiste(v1) || !verticeExiste(v2)){
            throw new IllegalArgumentException("O vértice v1 não existe");
        }

        // Vertice auxv1 = new Vertice(v1);
        // Vertice auxv2 = new Vertice(v2);
        // int index1 = listaVertices.indexOf(auxv1);
        // int index2 = listaVertices.indexOf(auxv2);

        // listaVertices.get(index1).listaAdjascencia.add(v2);
        // listaVertices.get(index2).listaAdjascencia.add(v1);
        //this.L++;
    }

    //@ requires listaVertices != null;
    //@ requires \forall int i; 0 <= i < listaVertices.size(); listaVertices.get(i) != null;
    //@ ensures (\exists int i; 0 <= i < listaVertices.size(); listaVertices.get(i).getN() == n) <==> \result == true;
    //@ ensures \forall int i; 0 <= i < listaVertices.size(); listaVertices.get(i) != null;
    //@ signals_only NullPointerException, RuntimeException;
    //@ pure
    Boolean verticeExiste(int n) {
        //@ maintaining 0 <= i <= listaVertices.size();
        //@ maintaining \forall int j; 0 <= j < listaVertices.size(); listaVertices.get(j) == \old(listaVertices.get(j));
        //@ loop_writes i;
        //@ decreases listaVertices.size() - i;
        for (int i=0; i < listaVertices.size(); i++){
            if(listaVertices.get(i).getN() == n){
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
    //@ requires \forall int i; 0 <= i < listaVertices.size(); listaVertices.get(i) != null;
    //@ ensures \forall int i; 0 <= i < listaVertices.size(); listaVertices.get(i) != null;
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

    //@ requires \forall int i; 0 <= i < listaVertices.size(); listaVertices.get(i) != null;
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

    //@ requires \forall int i; 0 <= i < listaVertices.size(); listaVertices.get(i) != null;
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

    //@ requires \forall int i; 0 <= i < listaVertices.size(); listaVertices.get(i) != null;
    //@ pure
    public List<Vertice> getListaVertices() {
        return listaVertices;
    }

    //@ requires lista != null;
    //@ ensures this.listaVertices == lista;
    //@ ensures this.listaVertices.size() == lista.size();
    //@ requires \forall int i; 0 <= i < lista.size(); lista.get(i) != null;
    //@ requires \forall int i; 0 <= i < listaVertices.size(); listaVertices.get(i) != null;
    //@ ensures this.listaVertices != null;
    //@ ensures \forall int i; 0 <= i < listaVertices.size(); listaVertices.get(i) != null;
    public void setListaVertices(List<Vertice> lista) {
        if (lista == null) {
            throw new IllegalArgumentException("Lista não pode ser nula!");
        }
        this.listaVertices = lista;
    }
}