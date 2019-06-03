function vec(arr){
	return new THREE.Vector3(arr[0], arr[1], arr[2])
}

meshes = []

function animate() {
	requestAnimationFrame(animate)
	meshes.forEach(mesh => {
		mesh.rotation.x += 0.006
		mesh.rotation.y += 0.06
		mesh.rotation.z += 0.00
	})
	window.renderer.render(window.scene, window.camera)
}

function addMeshFromQuads(q, color){
	var geometry = new THREE.Geometry()
	for (var i = 0; i < q.length - 3; i += 4){
		// Add our corners
			len = geometry.vertices.push(vec(q[i]), vec(q[i+1]), vec(q[i+2]), vec(q[i+3]))
		// Add quad as two triangles
			geometry.faces.push( new THREE.Face3(i, i+1, i+2) )
			geometry.faces.push( new THREE.Face3(i+2, i+3, i) )
	}
	geometry.computeBoundingSphere()
	geometry.computeBoundingBox()
	geometry.computeFaceNormals()

	var material = new THREE.MeshBasicMaterial({ color: color, transparent: true, opacity: 0.82, side: THREE.FrontSide })
	var mesh = new THREE.Mesh(geometry, material)
	meshes.push(mesh)
	window.scene.add(mesh)
}

window.camera = new THREE.PerspectiveCamera(70, window.innerWidth / window.innerHeight, 1, 10000)
window.camera.position.z = 3400
window.scene = new THREE.Scene()
window.renderer = new THREE.WebGLRenderer()
window.renderer.setPixelRatio(window.devicePixelRatio)
window.renderer.setSize(window.innerWidth, window.innerHeight)
document.body.appendChild(renderer.domElement)
