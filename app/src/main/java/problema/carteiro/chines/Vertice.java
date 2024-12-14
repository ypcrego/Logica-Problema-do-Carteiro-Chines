package problema.carteiro.chines;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

public class Vertice {
    //@ spec_public
    private int n; // Identificador do vértice

    //@ spec_public
    private double d;
    //@ spec_public
    private double rot;
    public List<Integer> listaAdjascencia; // Lista de vértices do vértice

    //@ public invariant listaAdjascencia != null;
    //@ public invariant listaAdjascencia.size() >= 0;
    //@ public invariant n >= 0;

    //@ normal_behavior
    //@ requires num >= 0;
    //@ ensures this.listaAdjascencia.size() == 0;
    //@ ensures this.listaAdjascencia != null;
    //@ ensures this.n >= 0;
    //@ ensures this.n == num;
    //@ ensures this != null;
    //@ pure
    public Vertice(int num){
        this.n = num;
        this.listaAdjascencia = new ArrayList<>();
    }
    //@ normal_behavior
    //@ requires ver != null;
    //@ requires ver.listaAdjascencia != null;
    //@ requires ver.listaAdjascencia.size() >= 0;
    //@ requires ver.n >= 0;

    //@ ensures this.listaAdjascencia.size() >= 0;
    //@ ensures this.listaAdjascencia != null;
    //@ ensures this.n >= 0;
    //@ ensures this != null;
    //@ ensures this.n == ver.n;
    //@ ensures this.d == ver.d;
    //@ ensures this.rot == ver.rot;
    //@ ensures \forall int i; 0 <= i < this.listaAdjascencia.size(); this.listaAdjascencia.get(i) == ver.listaAdjascencia.get(i);

    //@ pure
    public Vertice(Vertice ver){
        this.n = ver.n;
        this.d = ver.d;
        this.rot = ver.rot;
        this.listaAdjascencia = new ArrayList<>(ver.listaAdjascencia);
    }

    //@ requires 0 <= ver;
    //@ ensures \result == (\exists int i; 0<= i <listaAdjascencia.size(); listaAdjascencia.get(i) == ver);
    //@ pure
    public boolean adjacente(int ver){
        //@ maintaining 0 <= i <= this.listaAdjascencia.size();
        //@ maintaining \forall int j;  0 <= j <i; listaAdjascencia.get(j) != ver;
        //@ loop_writes i;
        //@ decreases this.listaAdjascencia.size() - i;
        for (int i=0; i < listaAdjascencia.size(); i++){
            if(listaAdjascencia.get(i) == ver){
                //@ assert listaAdjascencia.get(i) == ver;
                //@ assert \exists int j; 0 <= j < listaAdjascencia.size(); listaAdjascencia.get(j) == ver;
                return true;
            }
        }
        return false;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        Vertice vertice = (Vertice) o;
        return n == vertice.n;
    }

    // @Override //comentado pois não é necessário para o funcionamento do código
    // public int hashCode() {
    //     return Objects.hash(n);
    // }

    //getters e setters

    //@ normal_behavior
    //@ pure
    public int getN(){
        return this.n;
    }

    //@ requires num >= 0;
    //@ ensures this.n == num;
    public void setN(int num){
        this.n = num;
    }

    //@ pure
    public double getD(){
        return this.d;
    }

    public void setD(double d){
        this.d = d;
    }

    //@ pure
    public double getRot(){
        return this.rot;
    }

    public void setRot(double rot){
        this.rot = rot;
    }

    //@ pure
    public int getGrau(){
        return this.listaAdjascencia.size();
    }

    //@ pure
    public List<Integer> getListaAdjacencia(){
        return this.listaAdjascencia;
    }
}