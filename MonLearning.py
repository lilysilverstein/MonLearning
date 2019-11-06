import tensorflow as tf
from tensorflow import keras
import ast
import numpy as np
import matplotlib.pyplot as plt
from collections import Counter
from sklearn import svm
from sklearn import linear_model
import itertools
from sklearn.preprocessing import RobustScaler
import random
import glob
import os


all_data_folder_name = "TrainingData"

n_test = 300 # data to reserve for testing
n_val = 300 # data to reserve for validation

n_nodes_hl = [50, 50]   # nodes in the hidden layers
hm_epochs  = 40       # training times

test_trees_numerically = True

# main function
def main():
    test_choice, input_data = user_input_all()
    test_choice_in_string = [['.codim'], ['.dim'], ['.pivotTrees'], ['.pdim'], ['.reg']]    
    
    for choice_ext in test_choice_in_string[test_choice-1] :
        data = np.array([[input_data['.features'][i]#[[0,1,6,7,14]]
,input_data[choice_ext][i]] for i in range(len(input_data['.features']))])
       # data = np.array([[input_data['.features'][i], pdimclass(input_data[choice_ext][i])] for i in range(len(input_data['.features']))])
        n_classes = [16, 21, 9, 16, 103][test_choice-1]
        
        print("Number of Classes = ", n_classes)
        print("n_nodes_hl = ", n_nodes_hl)
        print("hm_epochs = ", hm_epochs)
        print("Total Number of Data = ", len(data))
        for i in range(1):
            if choice_ext == '.pivotTrees' and test_trees_numerically:
                train_and_test_trees_numerically(data, n_classes)
            else:
                train_and_test(data, n_classes)
        print("\n")

def regclass(n):
    if n < 15:
        return 0
    elif n < 37:
        return 1
    else:
        return 2

def dimclass(n):
    if n == 0:
        return 0
    elif n < 6:
        return 1
    elif n <10:
        return 2
    else:
        return 3

def pdimclass(n):
    if n < 3:
        return 0
    elif n < 8:
        return 1
    else:
        return 2
     
def train_and_test(data, n_classes):
    np.random.shuffle(data)
    n_test = int (0.1*len(data))
    n_train = len(data) - n_test
    assert n_train > 0
    train_data = data[0:n_train] # separate data into training data
    test_data = data[n_train:] # and testing data

    tfmodel = TFModel(n_classes, n_nodes_hl)
    tfmodel.train(train_data, epochs = hm_epochs)

    preds = tfmodel.test(test_data, n_classes)
    diff_from_correct_answer(preds, test_data, n_classes)

def choose_pivot_1(arr):
    return np.argwhere(arr == np.min(arr))[-1]

def choose_pivot_2(arr):
    opts = np.argwhere(arr == np.min(arr))
    for pref in [8, 7, 6, 4, 5, 2, 3, 0, 1]:
        if pref in opts:
            return pref

def train_and_test_trees_numerically(data, n_classes):
    np.random.shuffle(data)
    n_test = int (0.1*len(data))
    n_train = len(data) - n_test
    assert n_train > 0
    all_pivots_train = data[0:n_train] 
    all_pivots_test = data[n_train:] 
    just_pivots_train = [np.array([round(i) for i in l]) for l in all_pivots_train[:,1]]
    just_pivots_test = [np.array([round(i) for i in l]) for l in all_pivots_test[:,1]]
    best_pivot_train = [choose_pivot_2(L) for L in just_pivots_train]
    best_pivot_test = [choose_pivot_2(L) for L in just_pivots_test]   
    train_data = np.array([[all_pivots_train[i][0], best_pivot_train[i]] for i in range(n_train)])
    test_data = np.array([[all_pivots_test[i][0], best_pivot_test[i]] for i in range(n_test)])
    tfmodel = TFModel(n_classes,n_nodes_hl)
    SVMmodel = SVMModel()  

    # TF model
    tfmodel.train(train_data, epochs=hm_epochs)
    preds = tfmodel.test(test_data, n_classes)
    tree_error(just_pivots_test, preds)
    test_fixed_pivots(just_pivots_train + just_pivots_test) 

        
def tree_error(all_pivots, preds):
    print("total number of test data =", len(preds))
    n = 0
    m = 0
    k = 0
    maxk = 0
    for i in range(len(preds)):
        pred_tree = round(all_pivots[i][preds[i]],0)
        best_tree = round(min(all_pivots[i]),0)
        if (pred_tree == best_tree):
            n = n + 1
            m = m + 1
        else:
            p = (pred_tree - best_tree)/best_tree
            if p <= 0.05:
                m = m + 1
            k = k + p
            if (pred_tree - best_tree) > maxk:
                maxk = pred_tree - best_tree
    print(n," correct out of ",len(preds),"  ",round(100*n/len(preds),2),"%")
    print(m," good out of ",len(preds),"  ",round(100*m/len(preds),2),"%")   
    print("# of base cases is on average ",round(100*k/len(preds), 2),"% above optimal")
    print("worst extra base cases: ",maxk)
    l = 0
    for i in range(len(preds)):
        pred_tree = round(all_pivots[i][preds[i]],0)
        best_tree = round(min(all_pivots[i]),0)
        if (pred_tree == best_tree):
            continue
        else:
            l = l + pred_tree - best_tree
    print("extra base cases: ", l)
    print(Counter(preds))

def test_fixed_pivots(all_pivots):
    num = len(all_pivots)
    for j in range(0,9):
        n = 0
        m = 0
        k = 0
        maxk = 0
        print("pivot rule ",j)
        for i in range(num):
            pred_tree = round(all_pivots[i][j],0)
            best_tree = round(min(all_pivots[i]),0)
            if (pred_tree == best_tree):
                n = n + 1
                m = m + 1
            else:
                p = (pred_tree - best_tree)/best_tree
                if p <= 0.05:
                    m = m + 1
                k = k + p
                if (pred_tree - best_tree) > maxk:
                    maxk = pred_tree - best_tree
        print(n," correct out of ", num,"  ",round(100*n/num, 2),"%")
        print(m," good out of ", num,"  ",round(100*m/num, 2),"%")
        print("# of base cases is on average ",round(100*k/num, 2),"% above optimal")
        print("worst extra base cases: ",maxk)
        l = 0
        for i in range(num):
            pred_tree = round(all_pivots[i][j],0)
            best_tree = round(min(all_pivots[i]),0)
            if (pred_tree == best_tree):
                continue
            else:
                l = l + pred_tree - best_tree
        print("extra base cases: ", l)
    

# parent class for learning models
class Model:
    def preprocess(self,data): # a function for converting input file data to model input
        return np.array([np.array(datum) for datum in data])
    def train(self,data): pass # train the model on a list of input/output pairs
    def predict(self,datum): pass # predict the class of one input
    def test(self,data,n_classes): # test the model on a list of input/output pairs
        
        n_data = len(data)
        preds = [self.predict(datum) for datum in data[:,0]]
        num_acc = len([i for i in range(n_data) if preds[i] == data[i,1]])

        accuracy = num_acc/float(n_data)
        #print("accuracy = ", num_acc/float(n_data))
        return preds
            
# TensorFlow model
class TFModel(Model):
    def __init__(self, n_classes, n_nodes_hl):
        model = keras.Sequential()
        for i in range(len(n_nodes_hl)):
            model.add(keras.layers.Dense(n_nodes_hl[i], activation = tf.nn.relu))
        model.add(keras.layers.Dense(n_classes, activation = tf.nn.softmax))
        model.compile(optimizer=tf.optimizers.Adam(),
            loss = 'categorical_crossentropy',
            metrics = ['accuracy'])#,'mean_squared_error', 'mean_absolute_error'])
        self.model = model

    def train(self,data,epochs=hm_epochs):
        input_data = self.preprocess(data[:,0])
        tbCallBack = keras.callbacks.TensorBoard(log_dir='./Graph', histogram_freq=0, write_graph=True, write_images=True)
        self.history = self.model.fit(input_data, keras.utils.to_categorical(data[:,1]), verbose=0, validation_split = 0.1, epochs = epochs, callbacks=[tbCallBack])
        print(self.model.summary())

    def predict(self,datum):
        data = self.preprocess([datum])
        return np.argmax(self.model.predict(data)[0])


def user_input_all():
    test_choice = input("What do you want to test? \n 1. codimension \n 2. dimension \n 3. pivot rule \n 4. projective dimension \n 5. regularity \nYour choice: ")
    test_choice = int(test_choice)
    input_data = {}
    for folder in glob.glob(os.path.join(all_data_folder_name, '*')):
        input_data[folder] = {}

        for filename in glob.glob(os.path.join(folder, '*')):
            _, ext = os.path.splitext(filename) # get the extension of the file name
            if ext != '.ideals' and ext !='.ring':
                #print("folder = ", folder)
                #print("ext = ", ext)
                lines = tuple(open(filename, 'r')) 
                #print("total line = ", len(lines))
                input_data[folder][ext] = np.array([ast.literal_eval(lines[i]) for i in range(0, len(lines))])

    input_datas = {}
    inital_folder = folder

    for filename in glob.glob(os.path.join(folder, '*')):
        _, ext = os.path.splitext(filename) # get the extension of the file name

        if ext != '.ideals' and ext != '.ring':
            input_datas[ext] = input_data[inital_folder][ext]
            
           # print("extension = ", ext)
            for folder in glob.glob(os.path.join(all_data_folder_name, '*')):
                if folder != inital_folder and folder != all_data_folder_name+"/README":
                #    print("folder 2 = ", folder)

                    input_datas[ext] = np.concatenate((input_datas[ext], input_data[folder][ext]))
    

    return test_choice, input_datas

def diff_from_correct_answer(preds, data, n_classes):
    distance = np.zeros(n_classes)
    n_data = len(data)
    for i in range(n_data):
        distance[abs(preds[i]-data[i,1])] += 1 
    for i in range(n_classes):
        print("number of predict data that has distance ", i, " from the correct answer is ", distance[i])

def diff_from_correct_answer_detail(preds, data, n_classes):
    distance = np.zeros(n_classes)
    root_correct = np.zeros(shape=(n_classes+1))
    root_wrong = np.zeros(shape=(n_classes+1))
    root_ans_and_pred = np.zeros(shape=(n_classes+1,n_classes+1))
    n_data = len(data)
    for i in range(n_data):
        distance[abs(preds[i]-data[i,1])] += 1
        if  abs(preds[i]-data[i,1]) == 0: # if the prediction is correct
            root_correct[data[i,1]] += 1
        else: # if the prediction is not correct
            root_wrong[data[i,1]] += 1
            root_ans_and_pred[data[i,1],preds[i]] += 1

    for i in range(n_classes):
        print("number of predict data that has distance ", i, " from the correct answer is ", int(distance[i]))

    # prints triples of the form: actual class / predicted class / count
    # good for input to confusion matrix latex/tikz code
    for i in range(0,n_classes+1):
        if root_correct[i]!= 0  or root_wrong[i] != 0:
            print(i,"/",i,"/",int(root_correct[i]))
            for j in range(1,n_classes+1):
                if root_ans_and_pred[i,j] != 0:
                    print(i,"/",j,"/",int(root_ans_and_pred[i,j]))



if __name__== "__main__":
    
    main()
 
        
    
    
